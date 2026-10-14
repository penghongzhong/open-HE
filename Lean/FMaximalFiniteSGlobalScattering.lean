import FActualFiniteSContinuation
import FActualLeftFiniteSContinuation
import FActualTwoSidedFiniteSScattering

/-! Genuine finite S on the actual maximal lifespan, together with a pure
homogeneous H1 cap, forces globality and both actual scattering states.
The lifespan endpoints are constructed from the domain. Globality, endpoint
locations, source tails, W bounds, and limiting states are not premises.
The initial ground-state thresholds have not supplied the two criteria. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.MaximalFiniteSGlobal
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalSourceBounds
open MaximalTrajectory SobolevStretch StationarySelfTest Retarded ActualStrichartz
open EndpointOutput ForcingDomain
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath freeEnergyState

/-- One literal finite bound for the actual S size of every compact path in
this trajectory's own lifespan, including compact intervals on either side. -/
def UniformCompactS {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) (M : ℝ≥0) : Prop :=
  ∀ (b c : ℝ) (hbc : b ≤ c), ∀ hI : Set.Icc b c ⊆ U.domain,
    pathValueSize (intervalMeasure b c) (U.path hbc hI) ≤ (M : ℝ≥0∞)

def FiniteSOnDomain {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) : Prop :=
  ∃ M : ℝ≥0, UniformCompactS U M

/-- An interior point of a real open set has another point to its right. -/
theorem exists_mem_gt_of_open {D : Set ℝ} (hopen : IsOpen D) {a : ℝ} (ha : a ∈ D) :
    ∃ b ∈ D, a < b := by
  obtain ⟨l, u, haI, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds ha)
  obtain ⟨b, hab, hbu⟩ := exists_between haI.2
  exact ⟨b, hI ⟨haI.1.trans hab, hbu⟩, hab⟩

/-- An interior point of a real open set has another point to its left. -/
theorem exists_mem_lt_of_open {D : Set ℝ} (hopen : IsOpen D) {a : ℝ} (ha : a ∈ D) :
    ∃ b ∈ D, b < a := by
  obtain ⟨l, u, haI, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds ha)
  obtain ⟨b, hlb, hba⟩ := exists_between haI.1
  exact ⟨b, hI ⟨hlb, hba.trans haI.2⟩, hba⟩

/-- The supremum supplies the actual excluded finite right endpoint. -/
theorem right_endpoint_of_bddAbove {D : Set ℝ} (hopen : IsOpen D)
    (hconn : Set.OrdConnected D) {a : ℝ} (ha : a ∈ D) (hbdd : BddAbove D) :
    a < sSup D ∧ Set.Ico a (sSup D) ⊆ D ∧ sSup D ∉ D := by
  have hne : D.Nonempty := ⟨a, ha⟩
  obtain ⟨b, hb, hab⟩ := exists_mem_gt_of_open hopen ha
  refine ⟨hab.trans_le (le_csSup hbdd hb), ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, htc⟩ := exists_lt_of_lt_csSup hne ht.2
    exact hconn.out' ha hc ⟨ht.1, htc.le⟩
  · intro hs
    obtain ⟨c, hc, hsc⟩ := exists_mem_gt_of_open hopen hs
    exact (not_lt_of_ge (le_csSup hbdd hc)) hsc

/-- The infimum supplies the actual excluded finite left endpoint. -/
theorem left_endpoint_of_bddBelow {D : Set ℝ} (hopen : IsOpen D)
    (hconn : Set.OrdConnected D) {a : ℝ} (ha : a ∈ D) (hbdd : BddBelow D) :
    sInf D < a ∧ Set.Ioc (sInf D) a ⊆ D ∧ sInf D ∉ D := by
  have hne : D.Nonempty := ⟨a, ha⟩
  obtain ⟨b, hb, hba⟩ := exists_mem_lt_of_open hopen ha
  refine ⟨(csInf_le hbdd hb).trans_lt hba, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, hct⟩ := exists_lt_of_csInf_lt hne ht.1
    exact hconn.out' hc ha ⟨hct.le, ht.2⟩
  · intro hs
    obtain ⟨c, hc, hcs⟩ := exists_mem_lt_of_open hopen hs
    exact (not_lt_of_ge (csInf_le hbdd hc)) hcs

/-- Unboundedness in both directions fills an order-connected real set. -/
theorem eq_univ_of_unbounded {D : Set ℝ} (hconn : Set.OrdConnected D)
    (habove : ¬ BddAbove D) (hbelow : ¬ BddBelow D) : D = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro t
  obtain ⟨b, hb, hbt⟩ := not_bddBelow_iff.mp hbelow t
  obtain ⟨c, hc, htc⟩ := not_bddAbove_iff.mp habove t
  exact hconn.out' hb hc ⟨hbt.le, htc.le⟩

/-- Sobolev comparison turns only the homogeneous gradient cap into the
state norm cap required by the two accepted endpoint continuation theorems. -/
theorem state_cap_of_pure_gradient {K alpha kernel a G : ℝ} (hSob : OrdinarySobolev K)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hgradient : ∀ t ∈ U.domain, pureGradientNorm (U.state t) ≤ G) :
    ∀ t ∈ U.domain, ‖U.state t‖ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * G := by
  intro t ht
  exact (energyState_le_pureGradient hSob (U.state t)).trans
    (mul_le_mul_of_nonneg_left (hgradient t ht)
      (le_trans zero_le_one (le_max_right _ _)))

/-- The same compact S witness supplies both accepted finite-endpoint criteria. -/
theorem finite_endpoint_criteria_of_compact_s {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) (M : ℝ≥0) (hS : UniformCompactS U M)
    (T : ℝ) : FiniteSContinuation.FiniteSBefore U T ∧
      LeftFiniteSContinuation.FiniteSAfter U T := by
  constructor
  · exact ⟨M, fun b hab _ hI => hS a b hab hI⟩
  · exact ⟨M, fun b hba _ hI => hS b a hba hI⟩

/-- The same compact S witness supplies both genuine infinite-half-line criteria. -/
theorem infinite_s_criteria_of_compact_s {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) (M : ℝ≥0) (hS : UniformCompactS U M) :
    ActualScattering.FiniteSAfter U ∧ ActualLeftScattering.FiniteSBefore U := by
  constructor
  · exact ⟨M, fun b hab hI => hS a b hab hI⟩
  · exact ⟨M, fun b hba hI => hS b a hba hI⟩

/-- Actual maximality excludes each finite endpoint produced by native real
order topology. No endpoint, global lifespan, or conservation law is assumed. -/
theorem maximal_domain_eq_univ_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a G : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hmax : U.domain = maximalDomain alpha kernel a u0)
    (hgradient : ∀ t ∈ U.domain, pureGradientNorm (U.state t) ≤ G)
    (hfiniteS : FiniteSOnDomain U) : U.domain = Set.univ := by
  obtain ⟨M, hS⟩ := hfiniteS
  have hbound := state_cap_of_pure_gradient hSob U hgradient
  apply eq_univ_of_unbounded U.domain_connected
  · intro hbdd
    obtain ⟨haT, hU, hT⟩ := right_endpoint_of_bddAbove
      U.domain_open U.domain_connected U.center_mem hbdd
    exact FiniteSContinuation.maximal_finite_right_endpoint_not_finite_s
      hDensity hSob h0 hfree hret hefree heret hH u0 U hmax haT hU hT
      (fun t ht => hbound t (hU ht))
      (finite_endpoint_criteria_of_compact_s U M hS (sSup U.domain)).1
  · intro hbdd
    obtain ⟨hTa, hU, hT⟩ := left_endpoint_of_bddBelow
      U.domain_open U.domain_connected U.center_mem hbdd
    exact LeftFiniteSContinuation.maximal_finite_left_endpoint_not_finite_s
      hDensity hSob h0 hfree hret hefree heret hH u0 U hmax hTa hU hT
      (fun t ht => hbound t (hU ht))
      (finite_endpoint_criteria_of_compact_s U M hS (sInf U.domain)).2

/-- Globality and both graph/dotH1 scattering states for the constructed actual
maximal trajectory at the original datum. The only substantive additional
criteria are genuine finite S on its own domain and its pure dotH1 cap. -/
theorem actual_maximal_global_and_two_sided_scattering_of_finite_s
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a G : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState)
    (hgradient : ∀ t ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).domain,
      pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0).state t) ≤ G)
    (hfiniteS : FiniteSOnDomain
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0)) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0
    U.domain = Set.univ ∧ ∃ uMinus uPlus : EnergyState,
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) := by
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a u0
  have hglobal : U.domain = Set.univ := maximal_domain_eq_univ_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH u0 U rfl hgradient hfiniteS
  obtain ⟨M, hS⟩ := hfiniteS
  obtain ⟨hplus, hminus⟩ := infinite_s_criteria_of_compact_s U M hS
  exact ⟨hglobal, ActualTwoSidedScattering.exists_actual_two_sided_scattering_of_finite_s
    hDensity hSob h0 hfree hret hH U hglobal
    (fun t => hgradient t (hglobal.symm ▸ Set.mem_univ t)) hplus hminus⟩

end HartreeF.MaximalFiniteSGlobal
