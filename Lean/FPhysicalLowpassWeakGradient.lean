import FPhysicalLowEnergyRepresentatives

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap RealInnerProductSpace
namespace HartreeF.PhysicalLowpass
open EnergySpace EnergySpace.Highpass YoungSource SobolevStretch StationarySelfTest

/-- Exact transfer of an actual weak-gradient identity across two proved AE equalities. -/
theorem weakGradient_congr_ae {f g : V → ℝ} {U W : V → V}
    (h : HasWeakGradient f U) (hfg : f =ᵐ[volume] g) (hUW : U =ᵐ[volume] W) :
    HasWeakGradient g W := by
  refine ⟨h.function_local.congr hfg, h.gradient_local.congr hUW, ?_⟩
  intro v φ hφ hc
  calc
    _ = ∫ x : V, f x * fderiv ℝ φ x v := by
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      rw [hx]
    _ = -(∫ x : V, inner ℝ (U x) v * φ x) := h.integration_by_parts v φ hφ hc
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hUW] with x hx
      rw [hx]

def lowPhysicalProjectedGradient (A : ℂ →L[ℝ] ℝ) (q : Cutoff) {L : ℝ}
    (hL : 0 < L) (u : EnergyState) (x : V) : V :=
  ∑ j : Fin 3, A (lowPhysicalGradient q hL u j x) • coordinate j

theorem lowPhysicalProjectedGradient_same (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (A : ℂ →L[ℝ] ℝ) (q : Cutoff) {L : ℝ}
    (hL : 0 < L) (u : EnergyState) :
    lowPhysicalProjectedGradient A q hL u =ᵐ[volume]
      energyProjectedGradient A (lowEnergyState hDensity hSob q hL u) := by
  have hj : ∀ᵐ x ∂(volume : Measure V), ∀ j : Fin 3,
      lowPhysicalGradient q hL u j x = energyGradient j (lowEnergyState hDensity hSob q hL u) x :=
    ae_all_iff.mpr fun j => lowPhysicalGradient_same_gradient hDensity hSob q hL u j
  filter_upwards [hj] with x hx
  simp only [lowPhysicalProjectedGradient, energyProjectedGradient, hx]

theorem lowPhysical_hasWeakGradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (A : ℂ →L[ℝ] ℝ) (q : Cutoff) {L : ℝ}
    (hL : 0 < L) (u : EnergyState) :
    HasWeakGradient (fun x => A (lowPhysical q hL u x)) (lowPhysicalProjectedGradient A q hL u) := by
  apply weakGradient_congr_ae
    (energyState_hasWeakGradient A (lowEnergyState hDensity hSob q hL u))
    _ (lowPhysicalProjectedGradient_same hDensity hSob A q hL u).symm
  filter_upwards [lowPhysical_same_value hDensity hSob q hL u] with x hx
  rw [hx]

theorem lowPhysical_inDotH1 (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    InDotH1 (lowPhysical q hL u)
      (lowPhysicalProjectedGradient Complex.reCLM q hL u)
      (lowPhysicalProjectedGradient Complex.imCLM q hL u) := by
  refine ⟨?_, ?_, ?_, lowPhysical_hasWeakGradient hDensity hSob Complex.reCLM q hL u,
    lowPhysical_hasWeakGradient hDensity hSob Complex.imCLM q hL u⟩
  · exact (memLp_congr_ae (lowPhysical_same_value hDensity hSob q hL u)).mpr
      (Lp.memLp (energyValue (lowEnergyState hDensity hSob q hL u)))
  · exact (memLp_congr_ae (lowPhysicalProjectedGradient_same hDensity hSob Complex.reCLM q hL u)).mpr
      (energyProjectedGradient_memLp Complex.reCLM _)
  · exact (memLp_congr_ae (lowPhysicalProjectedGradient_same hDensity hSob Complex.imCLM q hL u)).mpr
      (energyProjectedGradient_memLp Complex.imCLM _)

/-- The SAME canonical low-state weak-gradient fields also lie in L-infinity. -/
theorem lowEnergyState_projectedGradient_memLp_top (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (A : ℂ →L[ℝ] ℝ) (q : Cutoff) {L : ℝ}
    (hL : 0 < L) (u : EnergyState) :
    MemLp (energyProjectedGradient A (lowEnergyState hDensity hSob q hL u)) ∞ volume := by
  apply memLp_finsetSum
  intro j _
  exact ((lowEnergyState_gradient_memLp_top hDensity hSob q hL u j).continuousLinearMap_comp A).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))

end HartreeF.PhysicalLowpass
