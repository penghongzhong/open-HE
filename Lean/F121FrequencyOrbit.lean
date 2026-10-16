import F121AffineCutoffEnergy

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121FrequencyOrbit
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open CriticalAffine Paper121SmallFrequency Paper121CutoffMaps Paper121AffineCutoff

theorem normalized_gradient_eq (r : ℝ) (hr : 0 < r) (y : Space) (u : EnergyState) :
    pureGradientNorm u = pureGradientNorm ((criticalAffineState r hr y).symm u) := by
  have he := criticalAffineState_pureGradientNorm r hr y ((criticalAffineState r hr y).symm u)
  rwa [(criticalAffineState r hr y).apply_symm_apply] at he

theorem compact_gradient_bddAbove {Q : Set EnergyState} (hQ : IsCompact Q) :
    BddAbove (pureGradientNorm '' Q) := by
  obtain ⟨C, _hC, hb⟩ := hQ.isBounded.exists_pos_norm_le
  refine ⟨Real.sqrt 3*C, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact (pureGradient_le_sqrt_three_energyState u).trans
    (mul_le_mul_of_nonneg_left (hb u hu) (Real.sqrt_nonneg _))

theorem normalized_orbit_gradient_bddAbove {ι : Type*} (U : ι → EnergyState)
    (r : ι → ℝ) (hr : ∀ s, 0 < r s) (y : ι → Space)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hq : ∀ s, (criticalAffineState (r s) (hr s) (y s)).symm (U s) ∈ Q) :
    BddAbove (range (fun s => pureGradientNorm (U s))) := by
  apply (compact_gradient_bddAbove hQ).mono
  rintro _ ⟨s, rfl⟩
  exact ⟨_, hq s, (normalized_gradient_eq (r s) (hr s) (y s) (U s)).symm⟩

/-- Every point of the same orbit is controlled, with arbitrary pointwise normalizers. -/
theorem normalized_orbit_small_pair (hD : OrdinaryH1Density) {K : ℝ}
    (hS : OrdinarySobolev K) (q : Cutoff) {ι : Type*} (U : ι → EnergyState)
    (r : ι → ℝ) (hr : ∀ s, 0 < r s) (hr1 : ∀ s, r s ≤ 1) (y : ι → Space)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hq : ∀ s, (criticalAffineState (r s) (hr s) (y s)).symm (U s) ∈ Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ) (hM : 0 < M), M ≤ δ → ∀ s,
      pureGradientNorm (lowEnergyCLM hD hS q hM (U s)) < ε ∧
      M*‖highValueL2CLM hD hS q hM (U s)‖ < ε := by
  obtain ⟨δ, hδ, hs⟩ := compact_small_frequency_pair hD hS q hQ hε
  refine ⟨δ, hδ, ?_⟩
  intro M hM hMδ s
  let f := (criticalAffineState (r s) (hr s) (y s)).symm (U s)
  have he : criticalAffineState (r s) (hr s) (y s) f = U s :=
    (criticalAffineState (r s) (hr s) (y s)).apply_symm_apply _
  have hκ : M*r s ≤ δ :=
    (mul_le_of_le_one_right hM.le (hr1 s)).trans hMδ
  have hf := hs (M*r s) (mul_pos hM (hr s)) hκ f (hq s)
  have hl := low_gradient_critical hD hS q (hr s) hM (y s) f
  have hh := weighted_high_critical hD hS q (hr s) hM (y s) f
  rw [he] at hl hh
  exact ⟨hl.trans_lt hf.1, hh.trans_lt hf.2⟩

end HartreeF.Paper121FrequencyOrbit
