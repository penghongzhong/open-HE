import FActualBackwardMildSolution
import FActualUniqueForwardSolution
import FFullZPathGluing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
namespace HartreeF.CenteredLocalSolution
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain EndpointOutput
open CriticalUniqueness CriticalPathRestriction CriticalPathGluing ActualBackwardLocalFixedPoint
open ActualLocalFixedPoint
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  hartreeDuhamelMap backwardHartreeDuhamelMap criticalPathIntervalSource
  chosenForwardFixedPoint chosenBackwardFixedPoint

/-- The literal backward mild equation on an actual finite critical path. -/
def IsBackwardMildHartreePath {a b : ℝ} (hab : a ≤ b) (alpha kernel : ℝ)
    (ub : EnergyState) (u : CriticalPath (intervalMeasure a b)) : Prop :=
  ∀ t : Set.Icc a b, ∀ φ : FreeFlow.Test,
    energyDistribution (energyPath _ u t) φ =
      FreeFlow.free ((t : ℝ)-b) (energyDistribution ub) φ - Complex.I *
        ∫ s in Set.Ioc (t : ℝ) b, ∫ x,
          (freeTest ((t : ℝ)-s) φ) x •
            forcing alpha kernel (energyValue (extendEnergyPath hab (energyPath _ u) s)) x

/-- A genuine two-sided local full-Z trajectory around any energy datum.
Both actual restrictions satisfy their literal signed Hartree Duhamel formulas.
Backward uniqueness, maximal lifespan and conservation are separate conclusions. -/
theorem exists_actual_centered_mild_fullZ (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (s0 : ℝ) (u0 : EnergyState) :
    ∃ a b : ℝ, ∃ ha : a < s0, ∃ hb : s0 < b,
      ∃ u : CriticalPath (intervalMeasure a b),
        energyPath _ u ⟨s0, ha.le, hb.le⟩ = u0 ∧ FullZPath u ∧
        IsMildHartreePath hb.le alpha kernel u0
          (restrictPath ha.le hb.le le_rfl u) ∧
        IsBackwardMildHartreePath ha.le alpha kernel u0
          (restrictPath le_rfl ha.le hb.le u) := by
  let l := chosenBackwardFixedPoint hDensity hSob h0 hfree hret hH s0 u0
  let r := chosenForwardFixedPoint hDensity hSob h0 hfree hret hH s0 u0
  have hLZ : FullZPath l.curve :=
    (congrArg (fun v : CriticalPath (intervalMeasure l.left s0) => FullZPath v) l.fixed).mp
      ⟨backwardHartreeDuhamelMap_endpointWitness hDensity hSob h0 hfree hret
        hefree heret hH l.left_lt.le u0 l.curve⟩
  have hRZ : FullZPath r.curve := fixedPoint_fullZ hDensity hSob h0 hfree hret
    hefree heret hH r.right_gt.le u0 r.curve r.fixed
  have hLmild : IsBackwardMildHartreePath l.left_lt.le alpha kernel u0 l.curve := by
    intro t φ
    exact (congrArg (fun v : CriticalPath (intervalMeasure l.left s0) =>
      energyDistribution (energyPath _ v t) φ) l.fixed).symm.trans
      (backwardHartreeDuhamelMap_literal_formula hDensity hSob h0 hfree hret hH
        l.left_lt.le u0 l.curve t φ)
  have hRmild : IsMildHartreePath r.right_gt.le alpha kernel u0 r.curve :=
    (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      r.right_gt.le u0 r.curve).mpr r.fixed
  have hm : energyPath _ l.curve ⟨s0, l.left_lt.le, le_rfl⟩ =
      energyPath _ r.curve ⟨s0, le_rfl, r.right_gt.le⟩ := l.terminal.trans r.initial.symm
  let u := gluePath l.left_lt.le r.right_gt.le l.curve r.curve hm
  refine ⟨l.left, r.right, l.left_lt, r.right_gt, u,
    (gluePath_middle l.left_lt.le r.right_gt.le l.curve r.curve hm).trans l.terminal,
    gluePath_fullZ l.left_lt.le r.right_gt.le l.curve r.curve hm hLZ hRZ, ?_, ?_⟩
  · exact Eq.mpr (congrArg (IsMildHartreePath r.right_gt.le alpha kernel u0)
      (restrict_gluePath_right l.left_lt.le r.right_gt.le l.curve r.curve hm)) hRmild
  · exact Eq.mpr (congrArg (IsBackwardMildHartreePath l.left_lt.le alpha kernel u0)
      (restrict_gluePath_left l.left_lt.le r.right_gt.le l.curve r.curve hm)) hLmild

end HartreeF.CenteredLocalSolution
