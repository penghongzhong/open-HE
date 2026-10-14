import FActualBackwardFixedPoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.ActualBackwardLocalFixedPoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] backwardHartreeDuhamelMap criticalPathIntervalSource
  energySubmodule criticalPathSubmodule energyPath energyDistribution

/-- Data produced by the actual fixed-point existence theorem. The fixed-point
and terminal identities are fields of this constructed output, not hypotheses
of the final existence consumer. -/
structure BackwardFixedPointData (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (b : ℝ) (u0 : EnergyState) where
  left : ℝ
  left_lt : left < b
  curve : CriticalPath (intervalMeasure left b)
  fixed : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH left_lt.le u0 curve = curve
  terminal : energyPath _ curve ⟨b, left_lt.le, le_rfl⟩ = u0

/-- Choose the already proved genuine fixed point behind a named data boundary
before adding endpoint norms or quantified distribution tests. -/
def chosenBackwardFixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (b : ℝ) (u0 : EnergyState) :
    BackwardFixedPointData hDensity hSob h0 hfree hret hH b u0 := by
  apply Classical.choice
  obtain ⟨a, hab, u, hfix, hinit⟩ := exists_actual_backward_fixedPoint
    hDensity hSob h0 hfree hret hH b u0
  exact ⟨⟨a, hab, u, hfix, hinit⟩⟩

end HartreeF.ActualBackwardLocalFixedPoint
