import FSameActualMassValue

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.MassAsymptotics
open EnergySpace EnergySpace.Highpass MassRecovery YoungSource Retarded SobolevStretch StationarySelfTest

variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
variable {C0 : ℝ} (hE : OrdinaryEndpointBound C0) (q : Cutoff)
variable {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
include hDensity hSob hE q hσ

/-- Quantitative budgets at every positive frequency force decay along the full real halfline.
Neither mass decay nor mass conservation is an input. -/
theorem actualValue_norm_tendsto_zero (F : EndpointOne) (u : ℝ → EnergyState) (a B : ℝ)
    (hNW : ∀ t ∈ Ici a, OriginalScalarNoWaste σ t (u t) F)
    (hB : ∀ t ∈ Ici a, pureGradientNorm (u t) ≤ B) :
    Tendsto (fun t : ℝ => ‖actualValue hDensity hSob hE q hσ F t (u t)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hfreq : Tendsto (fun L : ℝ => B / L) atTop (𝓝 0) := tendsto_id.const_div_atTop B
  obtain ⟨L, hL, hBL⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hfreq.eventually (gt_mem_nhds hε2))).exists
  have ht : Tendsto (fun t : ℝ => (C0 * cutoffYoungConstant q) * Real.sqrt L * tailNorm t F)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tailNorm_tendsto_zero F).const_mul ((C0 * cutoffYoungConstant q) * Real.sqrt L)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε2))
  refine ⟨max a T, fun t ht => ?_⟩
  have hta : t ∈ Ici a := le_trans (le_max_left a T) ht
  have hb := actualValue_budget hDensity hSob hE q hσ F t (u t) (hNW t hta) hL (hB t hta)
  have he := hT t (le_trans (le_max_right a T) ht)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- Decay of the actual L2 class itself follows from its norm, at all sufficiently late real times. -/
theorem actualValue_tendsto_zero (F : EndpointOne) (u : ℝ → EnergyState) (a B : ℝ)
    (hNW : ∀ t ∈ Ici a, OriginalScalarNoWaste σ t (u t) F)
    (hB : ∀ t ∈ Ici a, pureGradientNorm (u t) ≤ B) :
    Tendsto (fun t : ℝ => actualValue hDensity hSob hE q hσ F t (u t)) atTop (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr
    (actualValue_norm_tendsto_zero hDensity hSob hE q hσ F u a B hNW hB)

/-- The same canonical original L6 value has finite L2 mass at every time in the stated halfline,
and its genuine L2 norm tends to zero along the whole halfline. -/
theorem originalValue_mass_decay (F : EndpointOne) (u : ℝ → EnergyState) (a B : ℝ)
    (hNW : ∀ t ∈ Ici a, OriginalScalarNoWaste σ t (u t) F)
    (hB : ∀ t ∈ Ici a, pureGradientNorm (u t) ≤ B) :
    (∀ t ∈ Ici a, MemLp (energyValue (u t) : V → ℂ) 2 volume) ∧
    Tendsto (fun t : ℝ => (eLpNorm (energyValue (u t) : V → ℂ) 2 volume).toReal) atTop (𝓝 0) := by
  refine ⟨fun t ht => (originalValue_memLp_and_norm hDensity hSob hE q hσ F t (u t) (hNW t ht)).1, ?_⟩
  have hh := actualValue_norm_tendsto_zero hDensity hSob hE q hσ F u a B hNW hB
  apply hh.congr'
  filter_upwards [eventually_ge_atTop a] with t ht
  exact (originalValue_memLp_and_norm hDensity hSob hE q hσ F t (u t) (hNW t ht)).2.symm

theorem originalValue_mass_square_decay (F : EndpointOne) (u : ℝ → EnergyState) (a B : ℝ)
    (hNW : ∀ t ∈ Ici a, OriginalScalarNoWaste σ t (u t) F)
    (hB : ∀ t ∈ Ici a, pureGradientNorm (u t) ≤ B) :
    Tendsto (fun t : ℝ => ((eLpNorm (energyValue (u t) : V → ℂ) 2 volume).toReal)^2)
      atTop (𝓝 0) := by
  simpa only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using
    ((originalValue_mass_decay hDensity hSob hE q hσ F u a B hNW hB).2).pow 2

end HartreeF.MassAsymptotics
