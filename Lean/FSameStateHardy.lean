import FSchwartzSingularHardy
import FEnergySchwartzDensity
import FEnergyGradientTopology
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
Author candidate; exact native receipts and upstream review bindings govern status.
The final weighted function is the specified original u's canonical L6 value.
Only the existing OrdinaryH1Density and OrdinarySobolev K interfaces remain
explicit. There is no original-value L2, variance, radiality, Hardy, weighted
completion, representative-identification, or desired-limit-bound hypothesis.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.SameStateHardy
open EnergySpace SobolevStretch StationarySelfTest

/-- Literal weighted value of the original energy state, without re-completion. -/
def weightedValue (y : V) (u : EnergyState) (x : V) : ℂ :=
  ‖x - y‖⁻¹ • energyValue u x

lemma weightedValue_aestronglyMeasurable (y : V) (u : EnergyState) :
    AEStronglyMeasurable (weightedValue y u) volume :=
  (inverse_distance_measurable y).aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable (energyValue u))

lemma weightedValue_norm_sq (y : V) (u : EnergyState) (x : V) :
    ‖weightedValue y u x‖ ^ 2 = ‖energyValue u x‖ ^ 2 / ‖x - y‖ ^ 2 :=
  norm_inv_smul_sq _ (norm_nonneg _) _

/-- Genuine density plus L6 convergence produces actual Schwartz values
converging a.e. to the same canonical energyValue, along one subsequence. -/
theorem schwartz_approximation_ae_same_value (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    ∃ φ : ℕ → Test,
      Tendsto (fun n => schwartzEnergyState (φ n)) atTop (𝓝 u) ∧
      ∀ᵐ x ∂volume, Tendsto (fun n => φ n x) atTop (𝓝 (energyValue u x)) := by
  obtain ⟨ψ, hψ⟩ := schwartzEnergyState_approximation hDensity hSob u
  have hL6 : Tendsto (fun n => energyValue (schwartzEnergyState (ψ n)))
      atTop (𝓝 (energyValue u)) := (energyValue.continuous.tendsto u).comp hψ
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hL6
  obtain ⟨σ, hσ, hσae⟩ := hmeasure.exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      energyValue (schwartzEnergyState (ψ n)) x = ψ n x :=
    ae_all_iff.mpr (fun n => schwartzEnergyState_value_ae (ψ n))
  refine ⟨fun n => ψ (σ n), hψ.comp hσ.tendsto_atTop, ?_⟩
  filter_upwards [hall, hσae] with x hx hxt
  have heq : (fun n => ψ (σ n) x) =
      (fun n => energyValue (schwartzEnergyState (ψ (σ n))) x) :=
    funext (fun n => (hx (σ n)).symm)
  rw [heq]
  exact hxt

/-- Second Fatou step: both the weighted limit and the kinetic RHS are genuine
limits of the actual Schwartz approximation. No desired bound is an input. -/
theorem energy_hardy_square_lintegral_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (y : V) (u : EnergyState) :
    (∫⁻ x, ENNReal.ofReal (‖weightedValue y u x‖ ^ 2)) ≤
      ENNReal.ofReal (4 * gradientSquared u) := by
  obtain ⟨φ, hφstate, hφvalue⟩ := schwartz_approximation_ae_same_value hDensity hSob u
  have hgrad : Tendsto (fun n => gradientSquared (schwartzEnergyState (φ n)))
      atTop (𝓝 (gradientSquared u)) :=
    gradientSquared_tendsto (gradientTendsto_of_tendsto hφstate)
  have hB : Tendsto
      (fun n => ENNReal.ofReal (4 * gradientSquared (schwartzEnergyState (φ n))))
      atTop (𝓝 (ENNReal.ofReal (4 * gradientSquared u))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hgrad.const_mul 4)
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun n => ENNReal.ofReal (‖weightedSchwartz y (φ n) x‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖weightedValue y u x‖ ^ 2))) := by
    filter_upwards [hφvalue] with x hx
    have hw : Tendsto (fun n => weightedSchwartz y (φ n) x) atTop
        (𝓝 (weightedValue y u x)) := hx.const_smul (‖x - y‖⁻¹)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hw.norm.pow 2)
  exact lintegral_le_of_ae_tendsto_of_bounds
    (fun n => ((weightedSchwartz_aestronglyMeasurable y (φ n)).norm.pow 2).aemeasurable.ennreal_ofReal)
    hlim (fun n => schwartz_hardy_square_lintegral_bound y (φ n)) hB

/-- Same-canonical-value Hardy, including explicit finite squared integral. -/
theorem energy_hardy_finite_integral_and_memLp (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (y : V) (u : EnergyState) :
    (∫⁻ x, ENNReal.ofReal (‖weightedValue y u x‖ ^ 2)) < ∞ ∧
    Integrable (fun x => ‖weightedValue y u x‖ ^ 2) volume ∧
    (∫ x, ‖weightedValue y u x‖ ^ 2) ≤ 4 * gradientSquared u ∧
    MemLp (weightedValue y u) 2 volume ∧
    eLpNorm (weightedValue y u) 2 volume ≤ ENNReal.ofReal (2 * pureGradientNorm u) := by
  exact l2_of_square_lintegral_bound (weightedValue_aestronglyMeasurable y u)
    (gradientSquared_nonneg u) (energy_hardy_square_lintegral_bound hDensity hSob y u)

/-- Public translated Hardy theorem on every specified original energy state. -/
theorem energy_hardy_memLp_and_norm (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (y : V) (u : EnergyState) :
    MemLp (weightedValue y u) 2 volume ∧
    eLpNorm (weightedValue y u) 2 volume ≤ ENNReal.ofReal (2 * pureGradientNorm u) :=
  (energy_hardy_finite_integral_and_memLp hDensity hSob y u).2.2.2

/-- The displayed singular integral is genuine and finite, including at y. -/
theorem energy_hardy_integrable_and_bound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (y : V) (u : EnergyState) :
    Integrable (fun x : V => ‖energyValue u x‖ ^ 2 / ‖x - y‖ ^ 2) volume ∧
    (∫ x : V, ‖energyValue u x‖ ^ 2 / ‖x - y‖ ^ 2) ≤ 4 * gradientSquared u := by
  have h := energy_hardy_finite_integral_and_memLp hDensity hSob y u
  exact ⟨by simpa only [weightedValue_norm_sq] using h.2.1,
    by simpa only [weightedValue_norm_sq] using h.2.2.1⟩


/-- The actual L2 class of the same original weighted value. -/
def weightedL2 (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (y : V) (u : EnergyState) : Lp ℂ 2 (volume : Measure V) :=
  (energy_hardy_memLp_and_norm hDensity hSob y u).1.toLp (weightedValue y u)

/-- The class is bound to the literal original value, not a replacement state. -/
theorem weightedL2_coeFn (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (y : V) (u : EnergyState) :
    (weightedL2 hDensity hSob y u : V → ℂ) =ᵐ[volume] weightedValue y u :=
  (energy_hardy_memLp_and_norm hDensity hSob y u).1.coeFn_toLp

/-- The actual L2 representative has the same pure-gradient bound. -/
theorem weightedL2_norm_le (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (y : V) (u : EnergyState) :
    ‖weightedL2 hDensity hSob y u‖ ≤ 2 * pureGradientNorm u := by
  rw [weightedL2, Lp.norm_toLp]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (energy_hardy_memLp_and_norm hDensity hSob y u).2
  simpa only [ENNReal.toReal_ofReal
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pureGradientNorm_nonneg u))] using h

end HartreeF.SameStateHardy
