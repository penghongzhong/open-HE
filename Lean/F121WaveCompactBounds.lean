import FCompactFullZSFromSource

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped ENNReal Topology

namespace HartreeF.WaveRealization
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath CriticalUniqueness
open EndpointOutput FreeDataDependence CriticalSourceBounds ActualPerturbation CompactFullZS
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalGradient criticalPathIntervalSource hartreeDuhamelMap fullZSDifferenceSize

/-- The actual compact energy and critical-gradient caps produce a uniform
four-norm cap. Neither endpoint integrability nor scalar infinite-time source
integrability is an input. -/
theorem exists_compact_fullZS_cap (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B rho : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hB : 0 ≤ B) (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a b : ℝ} (hab : a ≤ b) (f : EnergyState)
      (u : CriticalPath (intervalMeasure a b)),
      IsMildHartreePath hab alpha kernel f u →
      ‖energyPath _ u‖ ≤ B → ‖fun j => criticalGradient _ j u‖ ≤ rho →
      fullZSDifferenceSize u 0 ≤ ENNReal.ofReal C := by
  let sourceChoice := criticalPathIntervalSource_cap_single_bound hDensity hSob hH
  let Cs : NNReal := Classical.choose sourceChoice
  let L := normComparisonConstant K
  let F : ℝ := (Cs:ℝ)*B^(2*alpha)*L^5*rho^5
  let A : ℝ := max B rho
  have hL : 0 ≤ L := (normComparisonConstant_pos hSob).le
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hA : 0 ≤ A := hB.trans (le_max_left _ _)
  let C : ℝ := (1+scalarSConstant K+3*Che)*A+3*Cre*F
  have hS := scalarSConstant_nonneg hSob
  have hChe := hefree.1
  have hCre := heret.1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro a b hab f u hmild huE huW
  have hsource : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤ F := by
    apply (pi_norm_le_iff_of_nonneg hF).mpr
    intro j
    exact (Classical.choose_spec sourceChoice) hab u B rho hB hrho huE huW j
  have hu : ‖u‖ ≤ A := by
    rw [criticalPath_norm]
    exact max_le (huE.trans (le_max_left _ _)) (huW.trans (le_max_right _ _))
  exact forward_fullZS_of_graph_source hDensity hSob h0 hfree hret hefree heret hH
    hab f u hA hF
    ((isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab f u).mp hmild)
    hu hsource

end HartreeF.WaveRealization
