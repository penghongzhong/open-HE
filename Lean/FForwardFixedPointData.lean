import FActualLocalFixedPoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.ActualLocalFixedPoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] hartreeDuhamelMap criticalPathIntervalSource
  energySubmodule criticalPathSubmodule energyPath energyDistribution

/-- Data produced by the actual fixed-point existence theorem. The fixed-point
and initial identities are fields of this constructed output, not hypotheses
of the final existence consumer. -/
structure ForwardFixedPointData (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (a : ℝ) (u0 : EnergyState) where
  right : ℝ
  right_gt : a < right
  curve : CriticalPath (intervalMeasure a right)
  fixed : hartreeDuhamelMap hDensity hSob h0 hfree hret hH right_gt.le u0 curve = curve
  initial : energyPath _ curve ⟨a, le_rfl, right_gt.le⟩ = u0

/-- Choose the already proved genuine fixed point behind a named data boundary
before adding endpoint norms or quantified distribution tests. -/
def chosenForwardFixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (a : ℝ) (u0 : EnergyState) :
    ForwardFixedPointData hDensity hSob h0 hfree hret hH a u0 := by
  apply Classical.choice
  obtain ⟨b, hab, u, hfix, hinit⟩ := exists_actual_forward_fixedPoint
    hDensity hSob h0 hfree hret hH a u0
  exact ⟨⟨b, hab, u, hfix, hinit⟩⟩

end HartreeF.ActualLocalFixedPoint
