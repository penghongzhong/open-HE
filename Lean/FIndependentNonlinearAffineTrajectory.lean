import FActualHartreeMildCovariance
import FActualMaximalMildTrajectory

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace HartreeF.NonlinearAffineTrajectoryReview
open EnergySpace CriticalPathSpace CriticalUniqueness ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open AffinePath AffineMixed CriticalAffine NonlinearAffine MaximalTrajectory
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  affineCriticalPath actualMaximalTrajectory LocalMildTrajectory.path IsMildHartreePath

/-- Take the actual compact path from the SAME original nonlinear trajectory.
Its transformed canonical curve, literal nonlinear mild equation, derived trace
and exact graph norm are conclusions, not additional source identities. -/
theorem local_mild_trajectory_affine_segment (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel s0 : ℝ} {f : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha kernel) (M : LocalMildTrajectory alpha kernel s0 f)
    {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
    (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆ M.domain) :
    ∃ v : CriticalPath (intervalMeasure A B),
      (∀ t : Icc A B, energyPath _ v t=affineState ha b (M.state (timeAffine a c t))) ∧
      IsMildHartreePath hAB alpha kernel (affineState ha b (M.state (timeAffine a c A))) v ∧
      energyPath _ v ⟨A,le_rfl,hAB⟩=affineState ha b (M.state (timeAffine a c A)) ∧
      ‖v‖=‖M.path (timeAffine_monotone ha c hAB) hI‖ := by
  let u := M.path (timeAffine_monotone ha c hAB) hI
  have hresult := affine_actual_mild_path hDensity hSob h0 hfree hret hH ha b c A B hAB
    (M.state (timeAffine a c A)) u (M.path_mild (timeAffine_monotone ha c hAB) hI)
  refine ⟨affineCriticalPath ha b c A B hAB u,?_,hresult.1,hresult.2.1,hresult.2.2⟩
  intro t
  exact (affineCriticalPath_energy_apply ha b c A B hAB u t).trans
    (congrArg (affineState ha b)
      (M.path_agrees (timeAffine_monotone ha c hAB) hI (intervalAffineHomeomorph ha c A B t)))

/-- Canonical actual-maximal specialization on a supplied original compact
segment. No maximal-domain covariance or extra scalar-L2 datum is assumed. -/
theorem actual_maximal_affine_segment (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (s0 : ℝ) (f : EnergyState) {a : ℝ} (ha : 0<a) (b : Space)
    (c A B : ℝ) (hAB : A≤B)
    (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f).domain) :
    ∃ v : CriticalPath (intervalMeasure A B),
      (∀ t : Icc A B, energyPath _ v t=affineState ha b
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f).state
          (timeAffine a c t))) ∧
      IsMildHartreePath hAB alpha kernel (affineState ha b
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f).state
          (timeAffine a c A))) v ∧
      energyPath _ v ⟨A,le_rfl,hAB⟩=affineState ha b
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f).state
          (timeAffine a c A)) ∧
      ‖v‖=‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f).path
        (timeAffine_monotone ha c hAB) hI‖ :=
  local_mild_trajectory_affine_segment hDensity hSob h0 hfree hret hH
    (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f) ha b c A B hAB hI

#print axioms local_mild_trajectory_affine_segment
#print axioms actual_maximal_affine_segment
end HartreeF.NonlinearAffineTrajectoryReview
