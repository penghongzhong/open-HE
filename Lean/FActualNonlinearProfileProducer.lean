import FFiniteProfileTimeBranch
import FInfiniteProfileTimeBranches

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.NonlinearProfile
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalUniqueness MaximalTrajectory
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest Retarded
open ActualStrichartz ForcingDomain EndpointOutput
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath
  IsMildHartreePath hartreeDuhamelMap criticalPathIntervalSource freeCriticalPath

/-- Single actual nonlinear profile from an explicitly normalized time regime.
The finite/positive-infinite/negative-infinite alternative is a hypothesis
about the supplied sequence, not a claim that an arbitrary sequence converges
without passing to a subsequence. The curve is the canonical actual maximal
Hartree trajectory, and its true-domain membership is part of the conclusion.
This theorem does not assert multi-profile reconstruction or decoupling. -/
theorem exists_actual_nonlinear_profile (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) (s : ℕ → ℝ)
    (hs : (∃ sstar : ℝ, Tendsto s atTop (𝓝 sstar)) ∨
      Tendsto s atTop atTop ∨ Tendsto s atTop atBot) :
    ∃ T : ℝ, ∃ f : EnergyState,
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
      (∀ᶠ n in atTop, s n ∈ M.domain) ∧
        Tendsto (fun n => ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖)
          atTop (𝓝 0) := by
  rcases hs with ⟨sstar, hfinite⟩ | hpositive | hnegative
  · exact ⟨sstar, freeEnergyState hDensity hSob sstar phi,
      finite_time_profile_approximation hDensity hSob h0 hfree hret hefree heret hH
        phi s sstar hfinite⟩
  · obtain ⟨T, f, _, hdomain, happrox⟩ :=
      positive_time_profile_approximation hDensity hSob h0 hfree hret hefree heret hH
        phi s hpositive
    exact ⟨T, f, hdomain, happrox⟩
  · obtain ⟨T, f, _, hdomain, happrox⟩ :=
      negative_time_profile_approximation hDensity hSob h0 hfree hret hefree heret hH
        phi s hnegative
    exact ⟨T, f, hdomain, happrox⟩

end HartreeF.NonlinearProfile
