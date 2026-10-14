import FActualMaximalMildTrajectory

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option diagnostics true
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.MaximalTrajectory
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction CriticalPathGluing CriticalUniqueness SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain EndpointOutput CenteredLocalSolution
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource restrictPath gluePath

/-- Internal endpoint gluing lemma. An already constructed actual closed mild
path extends to an actual open-interval trajectory through its right endpoint.
The centered local producers and true fixed-point concatenation are discharged
here. This lemma itself does not construct a closed path from a norm bound. -/
theorem closed_mildPath_extends_to_localTrajectory (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s0 T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hsT : s0 ≤ T) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure s0 T))
    (hu : IsMildHartreePath hsT alpha kernel u0 u) :
    ∃ V : LocalMildTrajectory alpha kernel s0 u0,
      Set.Icc s0 T ⊆ V.domain ∧
      (∀ t : Set.Icc s0 T, V.state t = energyPath _ u t) := by
  obtain ⟨a, d, ha, hd, p, hpcenter, _, hpmild⟩ :=
    exists_actual_centered_whole_mild_fullZ
      hDensity hSob h0 hfree hret hefree heret hH s0 u0
  let uT := energyPath (intervalMeasure s0 T) u ⟨T, hsT, le_rfl⟩
  obtain ⟨c, b, hc, hb, q, hqcenter, _, hqmild⟩ :=
    exists_actual_centered_whole_mild_fullZ
      hDensity hSob h0 hfree hret hefree heret hH T uT
  let l : CriticalPath (intervalMeasure a s0) := restrictPath le_rfl ha.le hd.le p
  let r : CriticalPath (intervalMeasure T b) := restrictPath hc.le hb.le le_rfl q
  have hpfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    (ha.le.trans hd.le) (energyPath _ p ⟨a, le_rfl, ha.le.trans hd.le⟩) p).mp hpmild
  have hqfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    (hc.le.trans hb.le) (energyPath _ q ⟨c, le_rfl, hc.le.trans hb.le⟩) q).mp hqmild
  have hufix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    hsT u0 u).mp hu
  have hlfix := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    le_rfl ha.le hd.le (energyPath _ p ⟨a, le_rfl, ha.le.trans hd.le⟩) p hpfix
  have hrfix := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    hc.le hb.le le_rfl (energyPath _ q ⟨c, le_rfl, hc.le.trans hb.le⟩) q hqfix
  have hlend : energyPath _ l ⟨s0, ha.le, le_rfl⟩ = u0 :=
    (restrictPath_energy le_rfl ha.le hd.le p ⟨s0, ha.le, le_rfl⟩).trans hpcenter
  have hrstart : energyPath _ r ⟨T, le_rfl, hb.le⟩ = uT :=
    (restrictPath_energy hc.le hb.le le_rfl q ⟨T, le_rfl, hb.le⟩).trans hqcenter
  have hrfix' : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hb.le uT r = r :=
    (congrArg (fun z : EnergyState =>
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hb.le z r) hqcenter).symm.trans hrfix
  have hmr : energyPath _ u ⟨T, hsT, le_rfl⟩ = energyPath _ r ⟨T, le_rfl, hb.le⟩ :=
    hrstart.symm
  let z : CriticalPath (intervalMeasure s0 b) := gluePath hsT hb.le u r hmr
  have hzfix := gluePath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    hsT hb.le u0 u r hmr hufix hrfix'
  have hzstart : energyPath _ z ⟨s0, le_rfl, hsT.trans hb.le⟩ = u0 :=
    actual_fixedPoint_initial hDensity hSob h0 hfree hret hH
      (hsT.trans hb.le) u0 z hzfix
  have hml : energyPath _ l ⟨s0, ha.le, le_rfl⟩ =
      energyPath _ z ⟨s0, le_rfl, hsT.trans hb.le⟩ := hlend.trans hzstart.symm
  have hzfix' : hartreeDuhamelMap hDensity hSob h0 hfree hret hH
      (hsT.trans hb.le) (energyPath _ l ⟨s0, ha.le, le_rfl⟩) z = z :=
    (congrArg (fun x : EnergyState =>
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH
        (hsT.trans hb.le) x z) hlend).trans hzfix
  let w : CriticalPath (intervalMeasure a b) := gluePath ha.le (hsT.trans hb.le) l z hml
  have hwfix := gluePath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    ha.le (hsT.trans hb.le) (energyPath _ p ⟨a, le_rfl, ha.le.trans hd.le⟩)
    l z hml hlfix hzfix'
  have hwstate : ∀ t : Set.Icc s0 T,
      energyPath _ w ⟨t, ha.le.trans t.property.1, t.property.2.trans hb.le⟩ =
        energyPath _ u t := by
    intro t
    exact (gluePath_energy ha.le (hsT.trans hb.le) l z hml
      ⟨t, ha.le.trans t.property.1, t.property.2.trans hb.le⟩).trans
      ((gluedEnergyPath_right ha.le (hsT.trans hb.le) l z hml
        ⟨t, t.property.1, t.property.2.trans hb.le⟩).trans
        ((gluePath_energy hsT hb.le u r hmr
          ⟨t, t.property.1, t.property.2.trans hb.le⟩).trans
          (gluedEnergyPath_left hsT hb.le u r hmr t)))
  have hwcenter : energyPath _ w ⟨s0, ha.le, hsT.trans hb.le⟩ = u0 :=
    (hwstate ⟨s0, le_rfl, hsT⟩).trans
      (actual_fixedPoint_initial hDensity hSob h0 hfree hret hH hsT u0 u hufix)
  have hwstart := actual_fixedPoint_initial hDensity hSob h0 hfree hret hH
    (ha.le.trans (hsT.trans hb.le))
    (energyPath _ p ⟨a, le_rfl, ha.le.trans hd.le⟩) w hwfix
  have hwmild : IsMildHartreePath (ha.le.trans (hsT.trans hb.le)) alpha kernel
      (energyPath _ w ⟨a, le_rfl, ha.le.trans (hsT.trans hb.le)⟩) w := by
    apply (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      (ha.le.trans (hsT.trans hb.le)) _ w).mpr
    exact (congrArg (fun x : EnergyState =>
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH
        (ha.le.trans (hsT.trans hb.le)) x w) hwstart).trans hwfix
  let V := localTrajectoryOfCenteredPath hDensity hSob h0 hfree hret hH
    ha (lt_of_le_of_lt hsT hb) u0 w hwcenter hwmild
  refine ⟨V, ?_, ?_⟩
  · intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  · intro t
    exact (extendEnergyPath_val (ha.le.trans (hsT.trans hb.le)) (energyPath _ w)
      ⟨t, ha.le.trans t.property.1, t.property.2.trans hb.le⟩).trans (hwstate t)

/-- Internal closed-path bridge: its right endpoint belongs to the actual
maximal domain, with no continuation assumption or auxiliary local producer. -/
theorem closed_mildPath_right_mem_maximalDomain (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s0 T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hsT : s0 ≤ T) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure s0 T))
    (hu : IsMildHartreePath hsT alpha kernel u0 u) :
    T ∈ maximalDomain alpha kernel s0 u0 := by
  obtain ⟨V, hV, _⟩ := closed_mildPath_extends_to_localTrajectory
    hDensity hSob h0 hfree hret hefree heret hH hsT u0 u hu
  exact subset_maximalDomain V (hV ⟨hsT, le_rfl⟩)

/-- If an actual trajectory omits the terminal point of a closed mild path
with its datum, it has a genuine strict extension. Agreement follows from
actual overlap uniqueness and full Z on every compact is inherited. -/
theorem closed_mildPath_gives_strict_trajectory_extension (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s0 T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hsT : s0 ≤ T) (u0 : EnergyState)
    (U : LocalMildTrajectory alpha kernel s0 u0) (hTU : T ∉ U.domain)
    (u : CriticalPath (intervalMeasure s0 T))
    (hu : IsMildHartreePath hsT alpha kernel u0 u) :
    ∃ V : LocalMildTrajectory alpha kernel s0 u0,
      U.domain ⊂ V.domain ∧ T ∈ V.domain ∧ Set.EqOn V.state U.state U.domain := by
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
  have hUV : U.domain ⊆ V.domain := subset_maximalDomain U
  have hTV : T ∈ V.domain := closed_mildPath_right_mem_maximalDomain
    hDensity hSob h0 hfree hret hefree heret hH hsT u0 u hu
  refine ⟨V, Set.ssubset_iff_subset_ne.mpr ⟨hUV, ?_⟩, hTV, ?_⟩
  · intro he
    exact hTU (he.symm ▸ hTV)
  · intro t ht
    exact LocalMildTrajectory.overlap_eq hDensity hSob h0 hfree hret hH V U (hUV ht) ht

/-- A finite point excluded from the actual maximal domain cannot be the
right endpoint of an actual closed mild path with the fixed initial datum. -/
theorem maximal_excluded_endpoint_has_no_closed_mildPath (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s0 T : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hsT : s0 ≤ T) (u0 : EnergyState)
    (hT : T ∉ maximalDomain alpha kernel s0 u0)
    (u : CriticalPath (intervalMeasure s0 T)) :
    ¬ IsMildHartreePath hsT alpha kernel u0 u := by
  intro hu
  exact hT (closed_mildPath_right_mem_maximalDomain
    hDensity hSob h0 hfree hret hefree heret hH hsT u0 u hu)

end HartreeF.MaximalTrajectory
