import FActualFiniteEndpointClosure
import FClosedMildPathMaximalExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory
namespace HartreeF.FiniteEndpoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded ForcingDomain CriticalUniqueness MaximalTrajectory EndpointOutput
open SobolevStretch StationarySelfTest ActualStrichartz
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution criticalPathIntervalSource hartreeDuhamelMap

/-- The bounded-graph-norm closure also has all the established endpoint Z
coordinates. This uses the same eight ordinary analytic premises. -/
theorem exists_closed_mild_fullZ_of_uniform_critical_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain)
    (hbound : UniformCriticalNormBefore U T M) :
    ∃ w : CriticalPath (intervalMeasure a T),
      (∀ t : Set.Icc a T, (t : ℝ) < T → energyPath _ w t = U.state t) ∧
      IsMildHartreePath haT.le alpha kernel u0 w ∧ FullZPath w := by
  obtain ⟨w, hw, hm⟩ := exists_closed_mild_of_uniform_critical_norm
    hDensity hSob h0 hfree hret hH u0 U haT hU hbound
  exact ⟨w, hw, hm, fixedPoint_fullZ hDensity hSob h0 hfree hret hefree heret hH
    haT.le u0 w ((isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      haT.le u0 w).mp hm)⟩

/-- Finite endpoint continuation is an actual local mild trajectory, obtained
by the closed-path producer and genuine local existence and concatenation. -/
theorem uniform_critical_norm_endpoint_mem_maximalDomain (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain)
    (hbound : UniformCriticalNormBefore U T M) :
    T ∈ maximalDomain alpha kernel a u0 := by
  obtain ⟨w, _, hm⟩ := exists_closed_mild_of_uniform_critical_norm
    hDensity hSob h0 hfree hret hH u0 U haT hU hbound
  exact closed_mildPath_right_mem_maximalDomain hDensity hSob h0 hfree hret
    hefree heret hH haT.le u0 w hm

/-- The same criterion supplies a strict actual extension when the original
trajectory omits its finite endpoint. -/
theorem exists_strict_extension_of_uniform_critical_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain) (hT : T ∉ U.domain)
    (hbound : UniformCriticalNormBefore U T M) :
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊂ V.domain ∧ T ∈ V.domain ∧ Set.EqOn V.state U.state U.domain := by
  obtain ⟨w, _, hm⟩ := exists_closed_mild_of_uniform_critical_norm
    hDensity hSob h0 hfree hret hH u0 U haT hU hbound
  exact closed_mildPath_gives_strict_trajectory_extension hDensity hSob h0 hfree hret
    hefree heret hH haT.le u0 U hT w hm

/-- At any finite excluded right endpoint of the actual maximal solution,
the actual compact E+W graph norms have no common finite bound. -/
theorem maximal_finite_right_endpoint_critical_norm_unbounded (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hmax : U.domain = maximalDomain alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain) (hT : T ∉ U.domain) :
    ∀ M : ℝ, ¬ UniformCriticalNormBefore U T M := by
  intro M hbound
  apply hT
  rw [hmax]
  exact uniform_critical_norm_endpoint_mem_maximalDomain hDensity hSob h0 hfree hret
    hefree heret hH u0 U haT hU hbound

#print axioms HartreeF.FiniteEndpoint.exists_closed_mild_fullZ_of_uniform_critical_norm
#print axioms HartreeF.FiniteEndpoint.uniform_critical_norm_endpoint_mem_maximalDomain
#print axioms HartreeF.FiniteEndpoint.exists_strict_extension_of_uniform_critical_norm
#print axioms HartreeF.FiniteEndpoint.maximal_finite_right_endpoint_critical_norm_unbounded
end HartreeF.FiniteEndpoint
