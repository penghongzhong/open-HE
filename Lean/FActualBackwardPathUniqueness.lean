import FContinuousBackwardEquality
import FBackwardSubintervalFixedPoint
import FActualBackwardLocalComparison
import FCriticalPathBackwardPairSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.CriticalUniqueness
open EnergySpace CriticalPathSpace CriticalPathBall CriticalPathRestriction
open ActualDuhamelPath IntervalTimeTransport BackwardSolutionComparison
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution backwardHartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- The terminal datum follows from the literal fixed-point equation itself. -/
theorem actual_backward_fixedPoint_terminal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hfix : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u) :
    energyPath _ u ⟨b, hab, le_rfl⟩ = u0 :=
  (congrArg (fun v : CriticalPath (intervalMeasure a b) =>
    energyPath _ v ⟨b, hab, le_rfl⟩) hfix).symm.trans
      (backwardHartreeDuhamelMap_terminal hDensity hSob h0 hfree hret hH hab u0 u)

/-- Any two literal Hartree fixed points in the actual critical path space
on the same finite interval and with the same terminal datum coincide. Small W caps
are produced on left internal intervals; none is assumed for the full paths. -/
theorem actual_backward_criticalPath_fixedPoint_unique (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u v : CriticalPath (intervalMeasure a b))
    (hu : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u)
    (hv : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v = v) : u = v := by
  let B : ℝ := max ‖energyPath _ u‖ ‖energyPath _ v‖
  have hB : 0 ≤ B :=
    (norm_nonneg (energyPath (intervalMeasure a b) u)).trans
      (le_max_left ‖energyPath (intervalMeasure a b) u‖ ‖energyPath (intervalMeasure a b) v‖)
  let choice := exists_actual_backward_local_fixedPoint_unique hDensity hSob h0 hfree hret hH hB
  let rho : ℝ := Classical.choose choice
  have hrho : 0 < rho := (Classical.choose_spec choice).1
  let f := extendEnergyPath hab (energyPath _ u)
  let g := extendEnergyPath hab (energyPath _ v)
  have ha : f b = g b := by
    have hfu := (extendEnergyPath_val hab (energyPath _ u) ⟨b, hab, le_rfl⟩).trans
      (actual_backward_fixedPoint_terminal hDensity hSob h0 hfree hret hH hab u0 u hu)
    have hgv := (extendEnergyPath_val hab (energyPath _ v) ⟨b, hab, le_rfl⟩).trans
      (actual_backward_fixedPoint_terminal hDensity hSob h0 hfree hret hH hab u0 v hv)
    exact hfu.trans hgv.symm
  have hall : Set.EqOn f g (Set.Icc a b) :=
    continuous_eqOn_of_backward_local f.continuous g.continuous ha (by
      intro r hr heq
      let small := exists_backward_pair_restriction_W_small hr.1 hr.2 u v rho hrho
      let d : ℝ := Classical.choose small
      have had : a ≤ d := Classical.choose (Classical.choose_spec small)
      have hdr : d < r := Classical.choose (Classical.choose_spec (Classical.choose_spec small))
      have hcaps := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec small))
      let ur := restrictPath had hdr.le hr.2 u
      let vr := restrictPath had hdr.le hr.2 v
      let ur0 : EnergyState := energyPath _ u ⟨r, had.trans hdr.le, hr.2⟩
      let vr0 : EnergyState := energyPath _ v ⟨r, had.trans hdr.le, hr.2⟩
      have hdata : ur0 = vr0 :=
        (extendEnergyPath_val hab (energyPath _ u)
          ⟨r, had.trans hdr.le, hr.2⟩).symm.trans
            (heq.trans (extendEnergyPath_val hab (energyPath _ v)
              ⟨r, had.trans hdr.le, hr.2⟩))
      have hufix := restrictPath_backward_hartree_fixedPoint hDensity hSob h0 hfree hret hH
        had hdr.le hr.2 u0 u hu
      have hvfix := restrictPath_backward_hartree_fixedPoint hDensity hSob h0 hfree hret hH
        had hdr.le hr.2 u0 v hv
      have hvfix' : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hdr.le ur0 vr = vr :=
        (congrArg (fun z : EnergyState =>
          backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hdr.le z vr) hdata).trans hvfix
      have hUE : ‖energyPath _ ur‖ ≤ B :=
        (restrictPath_energy_norm_le had hdr.le hr.2 u).trans (le_max_left _ _)
      have hVE : ‖energyPath _ vr‖ ≤ B :=
        (restrictPath_energy_norm_le had hdr.le hr.2 v).trans (le_max_right _ _)
      have hequal : ur = vr := (Classical.choose_spec choice).2.2
        hdr.le ur0 ur vr hufix hvfix' hUE hVE hcaps.1 hcaps.2
      refine ⟨d, hdr, ?_⟩
      intro s hs
      let st : Set.Icc d r := ⟨s, hs⟩
      have hsab : s ∈ Set.Icc a b := ⟨had.trans hs.1, hs.2.trans hr.2⟩
      have hsEq := congrArg (fun w : CriticalPath (intervalMeasure d r) => energyPath _ w st) hequal
      have hstates : energyPath _ u ⟨s, hsab⟩ = energyPath _ v ⟨s, hsab⟩ :=
        (restrictPath_energy had hdr.le hr.2 u st).symm.trans
          (hsEq.trans (restrictPath_energy had hdr.le hr.2 v st))
      exact (extendEnergyPath_val hab (energyPath _ u) ⟨s, hsab⟩).trans
        (hstates.trans (extendEnergyPath_val hab (energyPath _ v) ⟨s, hsab⟩).symm))
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  exact (extendEnergyPath_val hab (energyPath _ u) t).symm.trans
    ((hall t.property).trans (extendEnergyPath_val hab (energyPath _ v) t))

end HartreeF.CriticalUniqueness
