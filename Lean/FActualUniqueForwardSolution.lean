import FActualCriticalPathUniqueness
import FMildHartreeDefinition
import FForwardFixedPointData
import FEndpointProjectedGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
namespace HartreeF.CriticalUniqueness
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open ActualLocalFixedPoint EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource

/-- Uniqueness among all actual critical mild paths on the finite interval.
No W-smallness, cap or contraction premise remains in this statement. -/
theorem actual_mildPath_unique (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u v : CriticalPath (intervalMeasure a b))
    (hu : IsMildHartreePath hab alpha kernel u0 u)
    (hv : IsMildHartreePath hab alpha kernel u0 v) : u = v :=
  actual_criticalPath_fixedPoint_unique hDensity hSob h0 hfree hret hH hab u0 u v
    ((isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab u0 u).mp hu)
    ((isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab u0 v).mp hv)

/-- The constructed positive forward interval has a unique critical mild path,
and that same path has the full Z endpoint output and its exact initial value.
Continuous dependence, backward construction and maximal lifespan are separate. -/
theorem exists_actual_unique_forward_mild_fullZ (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (a : ℝ) (u0 : EnergyState) :
    ∃ b : ℝ, ∃ hab : a < b, ∃ u : CriticalPath (intervalMeasure a b),
      energyPath _ u ⟨a, le_rfl, hab.le⟩ = u0 ∧ FullZPath u ∧
      IsMildHartreePath hab.le alpha kernel u0 u ∧
      ∀ v : CriticalPath (intervalMeasure a b),
        IsMildHartreePath hab.le alpha kernel u0 v → v = u := by
  let w := chosenForwardFixedPoint hDensity hSob h0 hfree hret hH a u0
  have hm : IsMildHartreePath w.right_gt.le alpha kernel u0 w.curve :=
    (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      w.right_gt.le u0 w.curve).mpr w.fixed
  refine ⟨w.right, w.right_gt, w.curve, w.initial,
    fixedPoint_fullZ hDensity hSob h0 hfree hret hefree heret hH
      w.right_gt.le u0 w.curve w.fixed, hm, ?_⟩
  intro v hv
  exact actual_mildPath_unique hDensity hSob h0 hfree hret hH
    w.right_gt.le u0 v w.curve hv hm

end HartreeF.CriticalUniqueness
