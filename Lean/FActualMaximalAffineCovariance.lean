import FMaximalAffineDomain

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.MaximalAffine
open EnergySpace CriticalPathSpace CriticalUniqueness ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open AffinePath AffineMixed CriticalAffine NonlinearAffine MaximalTrajectory
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  affineCriticalPath LocalMildTrajectory.path IsMildHartreePath

/-- Full maximal-domain and same-trajectory covariance for the canonical
actual maximal solution. This is stronger than covariance on a supplied
compact segment and does not presume either solution is global. -/
theorem actualMaximalTrajectory_affine (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    {a : ℝ} (ha : 0<a) (b : Space) (c s0 : ℝ) (f : EnergyState) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
      ((s0-c)/a^2) (affineState ha b f)
    V.domain=(timeAffine a c) ⁻¹' U.domain ∧
      Set.EqOn V.state (fun t => affineState ha b (U.state (timeAffine a c t))) V.domain := by
  refine ⟨maximalDomain_affine_marked hDensity hSob h0 hfree hret hH ha b c s0 f,?_⟩
  intro t ht
  exact maximalState_affine_marked hDensity hSob h0 hfree hret hH ha b c s0 f ht

/-- Two-sided global existence is an equivalence derived from the exact
lifespan equality and the positive time homeomorphism, not an input. -/
theorem maximalDomain_affine_global_iff (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha kernel) {a : ℝ} (ha : 0<a) (b : Space) (c s0 : ℝ)
    (f : EnergyState) :
    maximalDomain alpha kernel ((s0-c)/a^2) (affineState ha b f)=Set.univ ↔
      maximalDomain alpha kernel s0 f=Set.univ := by
  rw [maximalDomain_affine_marked hDensity hSob h0 hfree hret hH ha b c s0 f]
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro s
    have ht : (timeAffineHomeomorph ha c).symm s∈
        (timeAffine a c) ⁻¹' maximalDomain alpha kernel s0 f := by rw [h]; trivial
    change timeAffine a c ((timeAffineHomeomorph ha c).symm s)∈
      maximalDomain alpha kernel s0 f at ht
    have he : timeAffine a c ((timeAffineHomeomorph ha c).symm s)=s :=
      (timeAffineHomeomorph ha c).apply_symm_apply s
    rwa [he] at ht
  · intro h
    rw [h,Set.preimage_univ]

end HartreeF.MaximalAffine
