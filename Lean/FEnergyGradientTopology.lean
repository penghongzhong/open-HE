import FEnergyGradientNorm
import Mathlib.Topology.Sequences

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.EnergySpace
open SobolevStretch

/-- The actual three coordinate L2 classes, with the Hilbert-product norm. -/
def gradientVector : EnergyState →ₗ[ℂ] PiLp 2 (fun _ : Fin 3 => L2) where
  toFun u := WithLp.toLp 2 (fun j => energyGradient j u)
  map_add' u v := by ext j; simp
  map_smul' c u := by ext j; simp

theorem pureGradientNorm_eq_norm_gradientVector (u : EnergyState) :
    pureGradientNorm u = ‖gradientVector u‖ := by
  rw [PiLp.norm_eq_of_L2]
  rfl

theorem pureGradientNorm_add_le (u v : EnergyState) :
    pureGradientNorm (u + v) ≤ pureGradientNorm u + pureGradientNorm v := by
  simp only [pureGradientNorm_eq_norm_gradientVector, map_add]
  exact norm_add_le _ _

theorem pureGradientNorm_smul (c : ℂ) (u : EnergyState) :
    pureGradientNorm (c • u) = ‖c‖ * pureGradientNorm u := by
  simp only [pureGradientNorm_eq_norm_gradientVector, map_smul, norm_smul]

/-- Actual L2 coordinate-gradient convergence to another C43 state. -/
def GradientTendsto {ι : Type*} (f : ι → EnergyState) (l : Filter ι)
    (g : EnergyState) : Prop :=
  ∀ j : Fin 3, Tendsto (fun n => energyGradient j (f n)) l (𝓝 (energyGradient j g))

theorem gradientTendsto_of_tendsto {ι : Type*} {f : ι → EnergyState}
    {l : Filter ι} {g : EnergyState} (h : Tendsto f l (𝓝 g)) :
    GradientTendsto f l g := fun j => (energyGradient j).continuous.tendsto g |>.comp h

theorem gradientSquared_tendsto {ι : Type*} {f : ι → EnergyState}
    {l : Filter ι} {g : EnergyState} (h : GradientTendsto f l g) :
    Tendsto (fun n => gradientSquared (f n)) l (𝓝 (gradientSquared g)) := by
  exact tendsto_finsetSum _ (fun j _ => (h j).norm.pow 2)

theorem pureGradientNorm_tendsto {ι : Type*} {f : ι → EnergyState}
    {l : Filter ι} {g : EnergyState} (h : GradientTendsto f l g) :
    Tendsto (fun n => pureGradientNorm (f n)) l (𝓝 (pureGradientNorm g)) :=
  (Real.continuous_sqrt.tendsto _).comp (gradientSquared_tendsto h)

theorem difference_gradientSquared_tendsto {ι : Type*} {f : ι → EnergyState}
    {l : Filter ι} {g : EnergyState} (h : GradientTendsto f l g) :
    Tendsto (fun n => gradientSquared (f n - g)) l (𝓝 0) := by
  have hh (j : Fin 3) : Tendsto (fun n => ‖energyGradient j (f n) - energyGradient j g‖^2)
      l (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((h j).sub (tendsto_const_nhds (x := energyGradient j g))).norm.pow 2
  simpa only [gradientSquared, map_sub, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => hh j)

theorem difference_pureGradientNorm_tendsto {ι : Type*} {f : ι → EnergyState}
    {l : Filter ι} {g : EnergyState} (h : GradientTendsto f l g) :
    Tendsto (fun n => pureGradientNorm (f n - g)) l (𝓝 0) := by
  simpa only [pureGradientNorm, Function.comp_def, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp (difference_gradientSquared_tendsto h)

/-- The L6 component is derived from actual gradient convergence. -/
theorem energyValue_tendsto_of_gradientTendsto {K : ℝ} (hSob : OrdinarySobolev K)
    {ι : Type*} {f : ι → EnergyState} {l : Filter ι} {g : EnergyState}
    (h : GradientTendsto f l g) :
    Tendsto (fun n => energyValue (f n)) l (𝓝 (energyValue g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun n => K^((6 : ℝ)⁻¹) * pureGradientNorm (f n - g)) l (𝓝 0) := by
    simpa only [mul_zero] using (difference_pureGradientNorm_tendsto h).const_mul (K^((6 : ℝ)⁻¹))
  apply squeeze_zero (fun _ => norm_nonneg _) _ hb
  intro n
  simpa only [map_sub] using energyValue_le_pureGradient hSob (f n - g)

/-- Coordinate-gradient convergence induces convergence in the existing Banach norm. -/
theorem tendsto_of_gradientTendsto {K : ℝ} (hSob : OrdinarySobolev K)
    {ι : Type*} {f : ι → EnergyState} {l : Filter ι} {g : EnergyState}
    (h : GradientTendsto f l g) : Tendsto f l (𝓝 g) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun n => max (K^((6 : ℝ)⁻¹)) 1 * pureGradientNorm (f n - g))
      l (𝓝 0) := by
    simpa only [mul_zero] using
      (difference_pureGradientNorm_tendsto h).const_mul (max (K^((6 : ℝ)⁻¹)) 1)
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => energyState_le_pureGradient hSob (f n - g)) hb

theorem tendsto_iff_gradientTendsto {K : ℝ} (hSob : OrdinarySobolev K)
    {ι : Type*} {f : ι → EnergyState} {l : Filter ι} {g : EnergyState} :
    Tendsto f l (𝓝 g) ↔ GradientTendsto f l g :=
  ⟨gradientTendsto_of_tendsto, tendsto_of_gradientTendsto hSob⟩

/-- The same topology can be tested by the literal pure-gradient difference norm. -/
theorem tendsto_iff_pureGradientNorm_sub {K : ℝ} (hSob : OrdinarySobolev K)
    {ι : Type*} {f : ι → EnergyState} {l : Filter ι} {g : EnergyState} :
    Tendsto f l (𝓝 g) ↔ Tendsto (fun n => pureGradientNorm (f n - g)) l (𝓝 0) := by
  constructor
  · intro h
    exact difference_pureGradientNorm_tendsto (gradientTendsto_of_tendsto h)
  · intro h
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hb : Tendsto (fun n => max (K^((6 : ℝ)⁻¹)) 1 * pureGradientNorm (f n - g))
        l (𝓝 0) := by
      simpa only [mul_zero] using h.const_mul (max (K^((6 : ℝ)⁻¹)) 1)
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => energyState_le_pureGradient hSob (f n - g)) hb

/-- Continuous actual gradients imply continuity of the same energy-state trajectory. -/
theorem trajectory_continuousOn_of_gradients {K : ℝ} (hSob : OrdinarySobolev K)
    {T : Type*} [TopologicalSpace T] {f : T → EnergyState} {I : Set T}
    (h : ∀ j : Fin 3, ContinuousOn (fun t => energyGradient j (f t)) I) :
    ContinuousOn f I := by
  intro t ht
  exact tendsto_of_gradientTendsto hSob (fun j => h j t ht)

/-- Closed actual gradient-energy bounds survive limits in the gradient topology. -/
theorem gradientSquared_bound_of_limit {ι : Type*} {f : ι → EnergyState}
    {l : Filter ι} [l.NeBot] {g : EnergyState} {C : ℝ}
    (h : GradientTendsto f l g) (hb : ∀ᶠ n in l, gradientSquared (f n) ≤ C) :
    gradientSquared g ≤ C := le_of_tendsto (gradientSquared_tendsto h) hb

/-- Compactness of the actual graph-norm energy space yields an actual gradient limit. -/
theorem compact_energy_subsequence {Q : Set EnergyState} (hQ : IsCompact Q)
    (f : ℕ → EnergyState) (hf : ∀ n, f n ∈ Q) :
    ∃ g ∈ Q, ∃ φ : ℕ → ℕ, StrictMono φ ∧ GradientTendsto (f ∘ φ) atTop g := by
  obtain ⟨g, hg, φ, hφ, hl⟩ := hQ.tendsto_subseq hf
  exact ⟨g, hg, φ, hφ, gradientTendsto_of_tendsto hl⟩

end HartreeF.EnergySpace
