import FActualUniqueForwardSolution
import FActualBackwardPathUniqueness
import FDirectionalHartreeRebasing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.MaximalTrajectory
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction CriticalUniqueness SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap backwardHartreeDuhamelMap
  criticalPathIntervalSource restrictPath

/-- An actual local Hartree solution on an open interval containing the given
datum. Every compact interval has a canonical E+W path with the literal mild
equation. No contraction cap, endpoint output, or maximality is a field. -/
structure LocalMildTrajectory (alpha kernel s0 : ℝ) (u0 : EnergyState) where
  domain : Set ℝ
  state : ℝ → EnergyState
  domain_open : IsOpen domain
  domain_connected : Set.OrdConnected domain
  center_mem : s0 ∈ domain
  continuous : ContinuousOn state domain
  initial : state s0 = u0
  compact : ∀ {a b : ℝ} (hab : a ≤ b), Set.Icc a b ⊆ domain →
    ∃ u : CriticalPath (intervalMeasure a b),
      (∀ t : Set.Icc a b, energyPath _ u t = state t) ∧
      IsMildHartreePath hab alpha kernel (state a) u

namespace LocalMildTrajectory
variable {alpha kernel s0 : ℝ} {u0 : EnergyState}

def path (U : LocalMildTrajectory alpha kernel s0 u0) {a b : ℝ}
    (hab : a ≤ b) (hI : Set.Icc a b ⊆ U.domain) :
    CriticalPath (intervalMeasure a b) := Classical.choose (U.compact hab hI)

theorem path_agrees (U : LocalMildTrajectory alpha kernel s0 u0) {a b : ℝ}
    (hab : a ≤ b) (hI : Set.Icc a b ⊆ U.domain) (t : Set.Icc a b) :
    energyPath _ (U.path hab hI) t = U.state t :=
  (Classical.choose_spec (U.compact hab hI)).1 t

theorem path_mild (U : LocalMildTrajectory alpha kernel s0 u0) {a b : ℝ}
    (hab : a ≤ b) (hI : Set.Icc a b ⊆ U.domain) :
    IsMildHartreePath hab alpha kernel (U.state a) (U.path hab hI) :=
  (Classical.choose_spec (U.compact hab hI)).2

/-- Full Z on compact intervals is an output of the actual endpoint estimates,
not an additional hypothesis in the definition of a competing solution. -/
theorem path_fullZ (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (U : LocalMildTrajectory alpha kernel s0 u0)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ U.domain) :
    FullZPath (U.path hab hI) :=
  fixedPoint_fullZ hDensity hSob h0 hfree hret hefree heret hH hab (U.state a)
    (U.path hab hI)
    ((isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      hab (U.state a) (U.path hab hI)).mp (U.path_mild hab hI))

/-- Compatibility on the overlap follows from actual finite-path uniqueness
in both time directions. No whole-interval W-smallness is assumed. -/
theorem overlap_eq (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (U V : LocalMildTrajectory alpha kernel s0 u0) {t : ℝ}
    (htU : t ∈ U.domain) (htV : t ∈ V.domain) : U.state t = V.state t := by
  by_cases hst : s0 ≤ t
  · have hIU : Set.Icc s0 t ⊆ U.domain := U.domain_connected.out' U.center_mem htU
    have hIV : Set.Icc s0 t ⊆ V.domain := V.domain_connected.out' V.center_mem htV
    let u := U.path hst hIU
    let v := V.path hst hIV
    have hu : IsMildHartreePath hst alpha kernel u0 u := by
      simpa only [U.initial] using U.path_mild hst hIU
    have hv : IsMildHartreePath hst alpha kernel u0 v := by
      simpa only [V.initial] using V.path_mild hst hIV
    have he := actual_mildPath_unique hDensity hSob h0 hfree hret hH hst u0 u v hu hv
    exact (U.path_agrees hst hIU ⟨t, hst, le_rfl⟩).symm.trans
      ((congrArg (fun w : CriticalPath (intervalMeasure s0 t) =>
        energyPath _ w ⟨t, hst, le_rfl⟩) he).trans
          (V.path_agrees hst hIV ⟨t, hst, le_rfl⟩))
  · have hts : t ≤ s0 := (lt_of_not_ge hst).le
    have hIU : Set.Icc t s0 ⊆ U.domain := U.domain_connected.out' htU U.center_mem
    have hIV : Set.Icc t s0 ⊆ V.domain := V.domain_connected.out' htV V.center_mem
    let u := U.path hts hIU
    let v := V.path hts hIV
    have hu := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      hts (U.state t) u).mp (U.path_mild hts hIU)
    have hv := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      hts (V.state t) v).mp (V.path_mild hts hIV)
    have hub := forwardFixedPoint_is_backward_at_terminal hDensity hSob h0 hfree hret hH
      hts (U.state t) u hu
    have hvb := forwardFixedPoint_is_backward_at_terminal hDensity hSob h0 hfree hret hH
      hts (V.state t) v hv
    have hUt : energyPath _ u ⟨s0, hts, le_rfl⟩ = u0 :=
      (U.path_agrees hts hIU ⟨s0, hts, le_rfl⟩).trans U.initial
    have hVt : energyPath _ v ⟨s0, hts, le_rfl⟩ = u0 :=
      (V.path_agrees hts hIV ⟨s0, hts, le_rfl⟩).trans V.initial
    have hu' : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hts u0 u = u :=
      (congrArg (fun z : EnergyState =>
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hts z u) hUt).symm.trans hub
    have hv' : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hts u0 v = v :=
      (congrArg (fun z : EnergyState =>
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hts z v) hVt).symm.trans hvb
    have he := actual_backward_criticalPath_fixedPoint_unique hDensity hSob h0 hfree hret hH
      hts u0 u v hu' hv'
    exact (U.path_agrees hts hIU ⟨t, le_rfl, hts⟩).symm.trans
      ((congrArg (fun w : CriticalPath (intervalMeasure t s0) =>
        energyPath _ w ⟨t, le_rfl, hts⟩) he).trans
          (V.path_agrees hts hIV ⟨t, le_rfl, hts⟩))

end LocalMildTrajectory
end HartreeF.MaximalTrajectory
