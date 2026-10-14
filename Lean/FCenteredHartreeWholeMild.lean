import FActualHartreeSolutionConcatenation
import FDirectionalHartreeRebasing
import FBackwardMildHartreeDefinition
import FActualCenteredMildSolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
namespace HartreeF.CriticalUniqueness
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction CriticalPathGluing SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap backwardHartreeDuhamelMap
  criticalPathIntervalSource restrictPath gluePath

/-- A canonical path satisfying the backward mild equation on its left piece
and the forward mild equation on its right piece is a whole forward mild path,
anchored at its own actual left endpoint. The common center datum is retained. -/
theorem centered_mild_is_forward_mild (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a c b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hac : a ≤ c) (hcb : c ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b))
    (hleft : IsBackwardMildHartreePath hac alpha kernel u0 (restrictPath le_rfl hac hcb u))
    (hright : IsMildHartreePath hcb alpha kernel u0 (restrictPath hac hcb le_rfl u)) :
    IsMildHartreePath (hac.trans hcb) alpha kernel
      (energyPath _ u ⟨a, le_rfl, hac.trans hcb⟩) u := by
  let l := restrictPath le_rfl hac hcb u
  let r := restrictPath hac hcb le_rfl u
  have hLb : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hac u0 l = l :=
    (isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hac u0 l).mp hleft
  have hLf := backwardFixedPoint_is_forward_at_initial hDensity hSob h0 hfree hret hH
    hac u0 l hLb
  have hRf : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb u0 r = r :=
    (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hcb u0 r).mp hright
  have hLc : energyPath _ l ⟨c, hac, le_rfl⟩ = u0 :=
    (congrArg (fun z : CriticalPath (intervalMeasure a c) =>
      energyPath _ z ⟨c, hac, le_rfl⟩) hLb).symm.trans
      (backwardHartreeDuhamelMap_terminal hDensity hSob h0 hfree hret hH hac u0 l)
  have hRrebase : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb
      (energyPath _ l ⟨c, hac, le_rfl⟩) r = r :=
    (congrArg (fun z : EnergyState =>
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb z r) hLc).trans hRf
  have hm : energyPath _ l ⟨c, hac, le_rfl⟩ = energyPath _ r ⟨c, le_rfl, hcb⟩ :=
    (restrictPath_energy le_rfl hac hcb u ⟨c, hac, le_rfl⟩).trans
      (restrictPath_energy hac hcb le_rfl u ⟨c, le_rfl, hcb⟩).symm
  have hwhole := gluePath_hartree_fixedPoint hDensity hSob h0 hfree hret hH hac hcb
    (energyPath _ l ⟨a, le_rfl, hac⟩) l r hm hLf hRrebase
  apply (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    (hac.trans hcb) (energyPath _ u ⟨a, le_rfl, hac.trans hcb⟩) u).mpr
  simpa only [l, r, restrictPath_initial, gluePath_restrictions] using hwhole

end HartreeF.CriticalUniqueness

namespace HartreeF.CenteredLocalSolution
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction CriticalUniqueness SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  restrictPath FullZPath CriticalUniqueness.IsMildHartreePath
  CriticalUniqueness.IsBackwardMildHartreePath CenteredLocalSolution.IsBackwardMildHartreePath

/-- The existing actual centered full-Z solution also solves the literal
Hartree equation on its whole interval, with its actual left state as datum.
This is the solution object needed when assembling a maximal lifespan. -/
theorem exists_actual_centered_whole_mild_fullZ (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (s0 : ℝ) (u0 : EnergyState) :
    ∃ a b : ℝ, ∃ ha : a < s0, ∃ hb : s0 < b,
      ∃ u : CriticalPath (intervalMeasure a b),
        energyPath _ u ⟨s0, ha.le, hb.le⟩ = u0 ∧ FullZPath u ∧
        CriticalUniqueness.IsMildHartreePath (ha.le.trans hb.le) alpha kernel
          (energyPath _ u ⟨a, le_rfl, ha.le.trans hb.le⟩) u := by
  have convertBackward {aa bb : ℝ} (hab : aa ≤ bb) (z : EnergyState)
      (v : CriticalPath (intervalMeasure aa bb)) :
      CenteredLocalSolution.IsBackwardMildHartreePath hab alpha kernel z v →
        CriticalUniqueness.IsBackwardMildHartreePath hab alpha kernel z v := by
    unfold CenteredLocalSolution.IsBackwardMildHartreePath
      CriticalUniqueness.IsBackwardMildHartreePath
    exact fun h => h
  let e := exists_actual_centered_mild_fullZ
    hDensity hSob h0 hfree hret hefree heret hH s0 u0
  let a : ℝ := Classical.choose e
  let ea := Classical.choose_spec e
  let b : ℝ := Classical.choose ea
  let eb := Classical.choose_spec ea
  let ha : a < s0 := Classical.choose eb
  let ec := Classical.choose_spec eb
  let hb : s0 < b := Classical.choose ec
  let ed := Classical.choose_spec ec
  let u : CriticalPath (intervalMeasure a b) := Classical.choose ed
  let hu := Classical.choose_spec ed
  have hleft' : CriticalUniqueness.IsBackwardMildHartreePath ha.le alpha kernel u0
      (restrictPath le_rfl ha.le hb.le u) :=
    convertBackward ha.le u0 (restrictPath le_rfl ha.le hb.le u) hu.2.2.2
  have hwhole := centered_mild_is_forward_mild hDensity hSob h0 hfree hret hH
    ha.le hb.le u0 u hleft' hu.2.2.1
  exact ⟨a, b, ha, hb, u, hu.1, hu.2.1, hwhole⟩

end HartreeF.CenteredLocalSolution
