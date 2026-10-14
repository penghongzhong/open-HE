import FActualMaximalMildTrajectory
import FEnergyFreeProperties

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
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath
  IsMildHartreePath hartreeDuhamelMap criticalPathIntervalSource freeCriticalPath

/-- Finite normalized-time branch. The nonlinear trajectory is anchored at the
actual limiting free value at sstar, and each sufficiently late sequence time
belongs to its true open maximal domain. The totalized values outside that
domain are irrelevant to the stated asymptotic approximation. -/
theorem finite_time_profile_approximation (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) (s : ℕ → ℝ) (sstar : ℝ)
    (hs : Tendsto s atTop (𝓝 sstar)) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
      sstar (freeEnergyState hDensity hSob sstar phi)
    (∀ᶠ n in atTop, s n ∈ M.domain) ∧
      Tendsto (fun n => ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖)
        atTop (𝓝 0) := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
    sstar (freeEnergyState hDensity hSob sstar phi)
  have hmem : M.domain ∈ 𝓝 sstar := M.domain_open.mem_nhds M.center_mem
  have hM : ContinuousAt M.state sstar := M.continuous.continuousAt hmem
  have hF : ContinuousAt (fun t => freeEnergyState hDensity hSob t phi) sstar :=
    (freeEnergyState_time_continuous hDensity hSob phi).continuousAt
  have hdiff : Tendsto (fun t => ‖M.state t-freeEnergyState hDensity hSob t phi‖)
      (𝓝 sstar) (𝓝 0) := by
    simpa only [M.initial, sub_self, norm_zero] using (hM.tendsto.sub hF.tendsto).norm
  exact ⟨hs.eventually hmem, hdiff.comp hs⟩

end HartreeF.NonlinearProfile
