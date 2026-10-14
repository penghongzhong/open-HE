import FLocalMildTrajectory
import FActualHartreeSolutionConcatenation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.MaximalTrajectory
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction CriticalPathGluing CriticalUniqueness SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource restrictPath gluePath

/-- Union of the domains of all actual local solutions with the fixed datum. -/
def maximalDomain (alpha kernel s0 : ℝ) (u0 : EnergyState) : Set ℝ :=
  ⋃ U : LocalMildTrajectory alpha kernel s0 u0, U.domain

/-- A choice of local state on the union; overlap uniqueness proves that the
choice does not affect any value in the union. Outside it, use the datum. -/
def maximalState (alpha kernel s0 : ℝ) (u0 : EnergyState) (t : ℝ) : EnergyState := by
  classical
  exact if ht : t ∈ maximalDomain alpha kernel s0 u0 then
    (Classical.choose (Set.mem_iUnion.mp ht)).state t else u0

variable {alpha kernel s0 : ℝ} {u0 : EnergyState}

theorem subset_maximalDomain (U : LocalMildTrajectory alpha kernel s0 u0) :
    U.domain ⊆ maximalDomain alpha kernel s0 u0 :=
  fun _ ht => Set.mem_iUnion.mpr ⟨U, ht⟩

theorem maximalDomain_open : IsOpen (maximalDomain alpha kernel s0 u0) :=
  isOpen_iUnion fun U => U.domain_open

theorem maximalDomain_connected : Set.OrdConnected (maximalDomain alpha kernel s0 u0) := by
  constructor
  intro a ha b hb t ht
  let U := Classical.choose (Set.mem_iUnion.mp ha)
  let V := Classical.choose (Set.mem_iUnion.mp hb)
  have haU : a ∈ U.domain := Classical.choose_spec (Set.mem_iUnion.mp ha)
  have hbV : b ∈ V.domain := Classical.choose_spec (Set.mem_iUnion.mp hb)
  by_cases hts : t ≤ s0
  · exact subset_maximalDomain U (U.domain_connected.out' haU U.center_mem ⟨ht.1, hts⟩)
  · exact subset_maximalDomain V
      (V.domain_connected.out' V.center_mem hbV ⟨(lt_of_not_ge hts).le, ht.2⟩)

theorem maximalState_agrees (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (U : LocalMildTrajectory alpha kernel s0 u0) {t : ℝ} (ht : t ∈ U.domain) :
    maximalState alpha kernel s0 u0 t = U.state t := by
  have htM := subset_maximalDomain U ht
  rw [maximalState, dite_eq_left htM]
  exact LocalMildTrajectory.overlap_eq hDensity hSob h0 hfree hret hH
    (Classical.choose (Set.mem_iUnion.mp htM)) U
    (Classical.choose_spec (Set.mem_iUnion.mp htM)) ht

/-- Continuity is inherited locally from any member containing the point. -/
theorem maximalState_continuous (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel) :
    ContinuousOn (maximalState alpha kernel s0 u0) (maximalDomain alpha kernel s0 u0) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  let U := Classical.choose (Set.mem_iUnion.mp ht)
  have htU : t ∈ U.domain := Classical.choose_spec (Set.mem_iUnion.mp ht)
  have hcont : ContinuousAt U.state t := U.continuous.continuousAt (U.domain_open.mem_nhds htU)
  apply hcont.congr_of_eventuallyEq
  filter_upwards [U.domain_open.mem_nhds htU] with s hs
  exact maximalState_agrees hDensity hSob h0 hfree hret hH U hs

/-- Each compact interval in the union has an actual mild CriticalPath.
Choose one local solution containing its left endpoint and one containing its
right endpoint. Glue their pieces at the fixed center and restrict the actual
whole fixed point. Zero-width pieces are allowed. -/
theorem maximalState_compact (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ maximalDomain alpha kernel s0 u0) :
    ∃ u : CriticalPath (intervalMeasure a b),
      (∀ t : Set.Icc a b, energyPath _ u t = maximalState alpha kernel s0 u0 t) ∧
      IsMildHartreePath hab alpha kernel (maximalState alpha kernel s0 u0 a) u := by
  have haM := hI ⟨le_rfl, hab⟩
  have hbM := hI ⟨hab, le_rfl⟩
  let U := Classical.choose (Set.mem_iUnion.mp haM)
  let V := Classical.choose (Set.mem_iUnion.mp hbM)
  have haU : a ∈ U.domain := Classical.choose_spec (Set.mem_iUnion.mp haM)
  have hbV : b ∈ V.domain := Classical.choose_spec (Set.mem_iUnion.mp hbM)
  have hminU : min a s0 ∈ U.domain := by
    by_cases has : a ≤ s0
    · simpa only [min_eq_left has] using haU
    · simpa only [min_eq_right (lt_of_not_ge has).le] using U.center_mem
  have hmaxV : max b s0 ∈ V.domain := by
    by_cases hsb : s0 ≤ b
    · simpa only [max_eq_left hsb] using hbV
    · simpa only [max_eq_right (lt_of_not_ge hsb).le] using V.center_mem
  have hL : Set.Icc (min a s0) s0 ⊆ U.domain := U.domain_connected.out' hminU U.center_mem
  have hR : Set.Icc s0 (max b s0) ⊆ V.domain := V.domain_connected.out' V.center_mem hmaxV
  let hac : min a s0 ≤ s0 := min_le_right a s0
  let hcb : s0 ≤ max b s0 := le_max_right b s0
  let l := U.path hac hL
  let r := V.path hcb hR
  have hlend : energyPath _ l ⟨s0, hac, le_rfl⟩ = u0 :=
    (U.path_agrees hac hL ⟨s0, hac, le_rfl⟩).trans U.initial
  have hrstart : energyPath _ r ⟨s0, le_rfl, hcb⟩ = u0 :=
    (V.path_agrees hcb hR ⟨s0, le_rfl, hcb⟩).trans V.initial
  have hm : energyPath _ l ⟨s0, hac, le_rfl⟩ = energyPath _ r ⟨s0, le_rfl, hcb⟩ :=
    hlend.trans hrstart.symm
  have hlfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    hac (U.state (min a s0)) l).mp (U.path_mild hac hL)
  have hrfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    hcb (V.state s0) r).mp (V.path_mild hcb hR)
  have hrdata : energyPath _ l ⟨s0, hac, le_rfl⟩ = V.state s0 := hlend.trans V.initial.symm
  have hrfix' : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb
      (energyPath _ l ⟨s0, hac, le_rfl⟩) r = r :=
    (congrArg (fun z : EnergyState =>
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb z r) hrdata).trans hrfix
  let w := gluePath hac hcb l r hm
  have hwfix := gluePath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    hac hcb (U.state (min a s0)) l r hm hlfix hrfix'
  have hwstate : ∀ t : Set.Icc (min a s0) (max b s0),
      energyPath _ w t = maximalState alpha kernel s0 u0 t := by
    intro t
    by_cases hts : (t : ℝ) ≤ s0
    · have htU : (t : ℝ) ∈ U.domain := hL ⟨t.property.1, hts⟩
      exact (gluePath_energy hac hcb l r hm t).trans
        ((gluedEnergyPath_left hac hcb l r hm ⟨t, t.property.1, hts⟩).trans
          ((U.path_agrees hac hL ⟨t, t.property.1, hts⟩).trans
            (maximalState_agrees hDensity hSob h0 hfree hret hH U htU).symm))
    · have hst : s0 ≤ (t : ℝ) := (lt_of_not_ge hts).le
      have htV : (t : ℝ) ∈ V.domain := hR ⟨hst, t.property.2⟩
      exact (gluePath_energy hac hcb l r hm t).trans
        ((gluedEnergyPath_right hac hcb l r hm ⟨t, hst, t.property.2⟩).trans
          ((V.path_agrees hcb hR ⟨t, hst, t.property.2⟩).trans
            (maximalState_agrees hDensity hSob h0 hfree hret hH V htV).symm))
  let v := restrictPath (min_le_left a s0) hab (le_max_left b s0) w
  have hvfix := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    (min_le_left a s0) hab (le_max_left b s0) (U.state (min a s0)) w hwfix
  have hdata := hwstate ⟨a, min_le_left a s0, hab.trans (le_max_left b s0)⟩
  refine ⟨v, ?_, ?_⟩
  · intro t
    exact (restrictPath_energy (min_le_left a s0) hab (le_max_left b s0) w t).trans
      (hwstate (intervalInclusion (min_le_left a s0) (le_max_left b s0) t))
  · apply (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      hab (maximalState alpha kernel s0 u0 a) v).mpr
    exact (congrArg (fun z : EnergyState =>
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab z v) hdata).symm.trans hvfix

end HartreeF.MaximalTrajectory
