import FSchwartzRegularizedHardy
import FHardyFatou
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Author candidate imported from preserved uncompiled proof text.
The initial draft preceded regularized producer compilation; author/final review
provider status and every native attempt are recorded separately.
The pole is excluded using volume.ae_ne; the regularized limit is never asserted
at x = y. Finiteness precedes all real-integral and L2 interpretations.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.SameStateHardy
open EnergySpace

/-- The ordinary inverse assigns zero at the null singleton. -/
def weightedSchwartz (y : V) (φ : Test) (x : V) : ℂ := ‖x - y‖⁻¹ • φ x

lemma inverse_distance_measurable (y : V) :
    Measurable (fun x : V => ‖x - y‖⁻¹) :=
  ((continuous_id.sub continuous_const).norm.measurable).inv

lemma weightedSchwartz_aestronglyMeasurable (y : V) (φ : Test) :
    AEStronglyMeasurable (weightedSchwartz y φ) volume :=
  (inverse_distance_measurable y).aestronglyMeasurable.smul φ.continuous.aestronglyMeasurable

lemma norm_inv_smul_sq (r : ℝ) (hr : 0 ≤ r) (z : ℂ) :
    ‖r⁻¹ • z‖ ^ 2 = ‖z‖ ^ 2 / r ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr), mul_pow,
    inv_pow, div_eq_mul_inv]
  ring

lemma weightedSchwartz_norm_sq (y : V) (φ : Test) (x : V) :
    ‖weightedSchwartz y φ x‖ ^ 2 = ‖φ x‖ ^ 2 / ‖x - y‖ ^ 2 :=
  norm_inv_smul_sq _ (norm_nonneg _) _

/-- First Fatou step. Its only estimate input is the actual upstream theorem,
invoked internally with ε_n > 0, rather than an exposed Hardy premise. -/
theorem schwartz_hardy_square_lintegral_bound (y : V) (φ : Test) :
    (∫⁻ x, ENNReal.ofReal (‖weightedSchwartz y φ x‖ ^ 2)) ≤
      ENNReal.ofReal (4 * gradientSquared (schwartzEnergyState φ)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let q : ℕ → V → ℝ := fun n x => ‖φ x‖ ^ 2 / (ε n + ‖x - y‖ ^ 2)
  have hq (n : ℕ) : Integrable (q n) volume ∧
      (∫ x, q n x) ≤ 4 * gradientSquared (schwartzEnergyState φ) :=
    RegularizedHardy.schwartz_regularized_hardy_integrable_and_bound (hε n) y φ
  have hqnonneg (n : ℕ) : 0 ≤ᵐ[volume] q n := by
    filter_upwards with x
    dsimp [q]
    have hpos := hε n
    positivity
  have hqbound (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (q n x)) ≤
        ENNReal.ofReal (4 * gradientSquared (schwartzEnergyState φ)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hq n).1 (hqnonneg n)]
    exact ENNReal.ofReal_le_ofReal (hq n).2
  have hlim : ∀ᵐ x ∂volume,
      Tendsto (fun n => ENNReal.ofReal (q n x)) atTop
        (𝓝 (ENNReal.ofReal (‖weightedSchwartz y φ x‖ ^ 2))) := by
    filter_upwards [(volume : Measure V).ae_ne y] with x hxy
    have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
    have hd : Tendsto (fun n => ε n + ‖x - y‖ ^ 2) atTop (𝓝 (‖x - y‖ ^ 2)) := by
      simpa only [zero_add] using hεt.add_const (‖x - y‖ ^ 2)
    have hquot : Tendsto (fun n => q n x) atTop (𝓝 (‖φ x‖ ^ 2 / ‖x - y‖ ^ 2)) :=
      tendsto_const_nhds.div hd (pow_ne_zero 2 hnorm)
    rw [weightedSchwartz_norm_sq]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hquot
  exact lintegral_le_of_ae_tendsto_of_bounds
    (fun n => (hq n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    hlim hqbound tendsto_const_nhds

/-- Actual finite squared integral, its real bound, L2 membership, and norm bound. -/
theorem schwartz_hardy_finite_integral_and_memLp (y : V) (φ : Test) :
    (∫⁻ x, ENNReal.ofReal (‖weightedSchwartz y φ x‖ ^ 2)) < ∞ ∧
    Integrable (fun x => ‖weightedSchwartz y φ x‖ ^ 2) volume ∧
    (∫ x, ‖weightedSchwartz y φ x‖ ^ 2) ≤ 4 * gradientSquared (schwartzEnergyState φ) ∧
    MemLp (weightedSchwartz y φ) 2 volume ∧
    eLpNorm (weightedSchwartz y φ) 2 volume ≤
      ENNReal.ofReal (2 * pureGradientNorm (schwartzEnergyState φ)) := by
  exact l2_of_square_lintegral_bound (weightedSchwartz_aestronglyMeasurable y φ)
    (gradientSquared_nonneg (schwartzEnergyState φ))
    (schwartz_hardy_square_lintegral_bound y φ)

/-- Convenient singular Schwartz Hardy output, with the constant exactly 2. -/
theorem schwartz_hardy_memLp_and_norm (y : V) (φ : Test) :
    MemLp (weightedSchwartz y φ) 2 volume ∧
    eLpNorm (weightedSchwartz y φ) 2 volume ≤
      ENNReal.ofReal (2 * pureGradientNorm (schwartzEnergyState φ)) :=
  (schwartz_hardy_finite_integral_and_memLp y φ).2.2.2

end HartreeF.SameStateHardy
