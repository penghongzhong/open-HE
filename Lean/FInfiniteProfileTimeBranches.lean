import FPositiveActualWaveOperator
import FNegativeActualWaveOperator

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
  IsMildHartreePath IsBackwardMildHartreePath hartreeDuhamelMap backwardHartreeDuhamelMap
  criticalPathIntervalSource freeCriticalPath

/-- A sequence of normalized times tending to positive infinity is realized
by the same actual maximal trajectory supplied by the positive wave producer.
The produced half-line inclusion implies eventual true-domain membership. -/
theorem positive_time_profile_approximation (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) (s : ℕ → ℝ) (hs : Tendsto s atTop atTop) :
    ∃ T : ℝ, ∃ f : EnergyState,
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
      Ici T ⊆ M.domain ∧ (∀ᶠ n in atTop, s n ∈ M.domain) ∧
        Tendsto (fun n => ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖)
          atTop (𝓝 0) := by
  obtain ⟨B, rho, T, f, _, _, _, hdomain, hasymptote, _⟩ :=
    WaveRealization.exists_positive_actual_wave_operator
      hDensity hSob h0 hfree hret hefree heret hH phi
  refine ⟨T, f, hdomain, ?_, hasymptote.comp hs⟩
  exact (hs.eventually (eventually_ge_atTop T)).mono fun _ hn => hdomain hn

/-- A sequence of normalized times tending to negative infinity is realized
by the same actual maximal trajectory supplied by the negative wave producer.
No time-reflection principle or forward globality is assumed. -/
theorem negative_time_profile_approximation (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) (s : ℕ → ℝ) (hs : Tendsto s atTop atBot) :
    ∃ T : ℝ, ∃ f : EnergyState,
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
      Iic T ⊆ M.domain ∧ (∀ᶠ n in atTop, s n ∈ M.domain) ∧
        Tendsto (fun n => ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖)
          atTop (𝓝 0) := by
  obtain ⟨B, rho, T, f, _, _, _, hdomain, hasymptote, _⟩ :=
    IncomingWaveRealization.exists_negative_actual_wave_operator
      hDensity hSob h0 hfree hret hefree heret hH phi
  refine ⟨T, f, hdomain, ?_, hasymptote.comp hs⟩
  exact (hs.eventually (eventually_le_atBot T)).mono fun _ hn => hdomain hn

end HartreeF.NonlinearProfile
