import FContinuousForwardEquality
import FHartreeSubintervalFixedPoint
import FActualLocalSolutionComparison
import FCriticalPathPairSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.CriticalUniqueness
open EnergySpace CriticalPathSpace CriticalPathBall CriticalPathRestriction
open ActualDuhamelPath IntervalTimeTransport LocalSolutionComparison
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- The initial datum follows from the literal fixed-point equation itself. -/
theorem actual_fixedPoint_initial (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u) :
    energyPath _ u ⟨a, le_rfl, hab⟩ = u0 :=
  (congrArg (fun v : CriticalPath (intervalMeasure a b) =>
    energyPath _ v ⟨a, le_rfl, hab⟩) hfix).symm.trans
      (hartreeDuhamelMap_initial hDensity hSob h0 hfree hret hH hab u0 u)

/-- Any two literal Hartree fixed points in the actual critical path space
on the same finite interval and with the same datum coincide. Small W caps
are produced on internal intervals; none is assumed for the full paths. -/
theorem actual_criticalPath_fixedPoint_unique (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u v : CriticalPath (intervalMeasure a b))
    (hu : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u)
    (hv : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 v = v) : u = v := by
  let B : ℝ := max ‖energyPath _ u‖ ‖energyPath _ v‖
  have hB : 0 ≤ B :=
    (norm_nonneg (energyPath (intervalMeasure a b) u)).trans
      (le_max_left ‖energyPath (intervalMeasure a b) u‖ ‖energyPath (intervalMeasure a b) v‖)
  let choice := exists_actual_local_fixedPoint_unique hDensity hSob h0 hfree hret hH hB
  let rho : ℝ := Classical.choose choice
  have hrho : 0 < rho := (Classical.choose_spec choice).1
  let f := extendEnergyPath hab (energyPath _ u)
  let g := extendEnergyPath hab (energyPath _ v)
  have ha : f a = g a := by
    have hfu := (extendEnergyPath_val hab (energyPath _ u) ⟨a, le_rfl, hab⟩).trans
      (actual_fixedPoint_initial hDensity hSob h0 hfree hret hH hab u0 u hu)
    have hgv := (extendEnergyPath_val hab (energyPath _ v) ⟨a, le_rfl, hab⟩).trans
      (actual_fixedPoint_initial hDensity hSob h0 hfree hret hH hab u0 v hv)
    exact hfu.trans hgv.symm
  have hall : Set.EqOn f g (Set.Icc a b) :=
    continuous_eqOn_of_forward_local f.continuous g.continuous ha (by
      intro r hr heq
      let small := exists_forward_pair_restriction_W_small hr.1 hr.2 u v rho hrho
      let d : ℝ := Classical.choose small
      have hrd : r < d := Classical.choose (Classical.choose_spec small)
      have hdb : d ≤ b := Classical.choose (Classical.choose_spec (Classical.choose_spec small))
      have hcaps := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec small))
      let ur := restrictPath hr.1 hrd.le hdb u
      let vr := restrictPath hr.1 hrd.le hdb v
      let ur0 : EnergyState := energyPath _ u ⟨r, hr.1, hrd.le.trans hdb⟩
      let vr0 : EnergyState := energyPath _ v ⟨r, hr.1, hrd.le.trans hdb⟩
      have hdata : ur0 = vr0 :=
        (extendEnergyPath_val hab (energyPath _ u)
          ⟨r, hr.1, hrd.le.trans hdb⟩).symm.trans
            (heq.trans (extendEnergyPath_val hab (energyPath _ v)
              ⟨r, hr.1, hrd.le.trans hdb⟩))
      have hufix := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
        hr.1 hrd.le hdb u0 u hu
      have hvfix := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
        hr.1 hrd.le hdb u0 v hv
      have hvfix' : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hrd.le ur0 vr = vr :=
        (congrArg (fun z : EnergyState =>
          hartreeDuhamelMap hDensity hSob h0 hfree hret hH hrd.le z vr) hdata).trans hvfix
      have hUE : ‖energyPath _ ur‖ ≤ B :=
        (restrictPath_energy_norm_le hr.1 hrd.le hdb u).trans (le_max_left _ _)
      have hVE : ‖energyPath _ vr‖ ≤ B :=
        (restrictPath_energy_norm_le hr.1 hrd.le hdb v).trans (le_max_right _ _)
      have hequal : ur = vr := (Classical.choose_spec choice).2.2
        hrd.le ur0 ur vr hufix hvfix' hUE hVE hcaps.1 hcaps.2
      refine ⟨d, hrd, ?_⟩
      intro s hs
      let st : Set.Icc r d := ⟨s, hs⟩
      have hsab : s ∈ Set.Icc a b := ⟨hr.1.trans hs.1, hs.2.trans hdb⟩
      have hsEq := congrArg (fun w : CriticalPath (intervalMeasure r d) => energyPath _ w st) hequal
      have hstates : energyPath _ u ⟨s, hsab⟩ = energyPath _ v ⟨s, hsab⟩ :=
        (restrictPath_energy hr.1 hrd.le hdb u st).symm.trans
          (hsEq.trans (restrictPath_energy hr.1 hrd.le hdb v st))
      exact (extendEnergyPath_val hab (energyPath _ u) ⟨s, hsab⟩).trans
        (hstates.trans (extendEnergyPath_val hab (energyPath _ v) ⟨s, hsab⟩).symm))
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  exact (extendEnergyPath_val hab (energyPath _ u) t).symm.trans
    ((hall t.property).trans (extendEnergyPath_val hab (energyPath _ v) t))

end HartreeF.CriticalUniqueness
