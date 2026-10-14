import FLocalMildTrajectory
import FOriginalMildToTensorPDE
import FCompactSupportIntervalLocalization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.HartreeMildPDEProducer
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport ForcingDomain
open LinearWeakEquation CriticalUniqueness CompactPDEDualBridge MaximalTrajectory

variable (hDensity : OrdinaryH1Density) {K alpha c s0 C0 Ch Cr : ℝ}
  (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hgen : OrdinaryFreeDistributionScalarGenerator)
  {u0 : EnergyState} (U : LocalMildTrajectory alpha c s0 u0)

include hDensity hSob h0 hfree hret hgen in
/-- The ORIGINAL LocalMildTrajectory supplies its own finite path, actual all-time
state equality and literal mild formula. No same-state or PDE contract is assumed. -/
theorem localMildTrajectory_interval_tensorPDE {a b : ℝ}
    (hab : a ≤ b) (hI : Icc a b ⊆ U.domain) :
    CompactHartreeTensorPDE hH U.state (Ioo a b) :=
  actual_original_tensorPDE_of_mild hDensity hSob hH h0 hfree hret hab
    (U.path hab hI) (U.state a) hgen U.state
    (U.path_agrees hab hI) (U.path_mild hab hI)

include hDensity hSob h0 hfree hret hgen in
/-- Every compactly supported time test in the EXACT original open domain is
localized strictly inside a closed finite interval on which the original trajectory
has its own mild CriticalPath. Thus the original forcing and state solve the actual
tensor PDE throughout that domain, without endpoint tests or extensions of u. -/
theorem localMildTrajectory_domain_tensorPDE :
    CompactHartreeTensorPDE hH U.state U.domain := by
  intro η hη hc hs φ hφ
  obtain ⟨a, b, hab, hI, hηI⟩ := compact_subset_exists_closed_interval
    U.domain_open U.domain_connected ⟨s0, U.center_mem⟩ hc hs
  exact localMildTrajectory_interval_tensorPDE hDensity hSob hH h0 hfree hret hgen U
    hab.le hI η hη hc hηI φ hφ

end HartreeF.HartreeMildPDEProducer
