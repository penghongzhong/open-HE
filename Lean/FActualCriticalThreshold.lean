import FActualFiniteSCurveFinite
import FMarkedBelowEnergyTransport
import FPositiveSmallEnergyScattering
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual critical infimum on the original stable branch.  The positive
seed, finite-S/finite-X bridge and quantitative W gap are produced from their
actual predecessors.  No uniform scattering bound on a lower-energy sublevel
is assumed.  Author source, UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualCriticalThreshold
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz DirectionalCoercivity R2Global
  DynamicSharpW FiniteSActualX
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- Both original strict W thresholds, on the actual homogeneous state. -/
def StableDatum (alpha : ℝ) (f : EnergyState) : Prop :=
  totalEnergy alpha f < totalEnergy alpha (normalizedBubbleState alpha) ∧
    pureGradientNorm f < pureGradientNorm (normalizedBubbleState alpha)

theorem trapping_factor_pos {alpha : ℝ} (hH : SharpOrdinaryHLS alpha) :
    0 < 2*(3+alpha)/(2+alpha) := by
  have ha := hH.order_pos
  positivity

theorem stable_kinetic_le_energy {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    {f : EnergyState} (hf : StableDatum alpha f) :
    gradientSquared f ≤ (2*(3+alpha)/(2+alpha))*totalEnergy alpha f :=
  state_kinetic_le_energy_below_W hOrd hH hS f
    ((pureGradientNorm_lt_iff_gradientSquared_lt _ _).mp hf.2).le

theorem stable_energy_nonneg {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    {f : EnergyState} (hf : StableDatum alpha f) : 0 ≤ totalEnergy alpha f := by
  have hp := trapping_factor_pos hH
  have he := (gradientSquared_nonneg f).trans (stable_kinetic_le_energy hOrd hH hS hf)
  nlinarith

/-- The actual calibration, including the original normalization of W. -/
theorem trapping_factor_ground_energy (hDensity : OrdinaryH1Density) {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) :
    (2*(3+alpha)/(2+alpha))*totalEnergy alpha (normalizedBubbleState alpha) =
      gradientSquared (normalizedBubbleState alpha) := by
  rw [normalizedBubbleState_energy hOrd hH hS hDensity,
    normalizedBubbleState_kinetic hH.order_pos hH.order_lt_three]
  unfold thresholdEnergy
  have ha := hH.order_pos
  have htwo : 2+alpha ≠ 0 := by linarith
  have hthree : 3+alpha ≠ 0 := by linarith
  field_simp [htwo, hthree] <;> ring

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))

/-- Badness is measured on the genuine native lifespan, not on the totalized
state outside that domain.  The defining mark is exactly time zero. -/
def BadDatum (f : EnergyState) : Prop :=
  StableDatum alpha f ∧ ¬ FiniteSOnDomain
    (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f)

def badEnergies : Set ℝ :=
  {e | ∃ f : EnergyState, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f ∧
    totalEnergy alpha f = e}

def criticalLevel : ℝ := sInf (badEnergies hDensity hSob h0 hfree hret hefree heret hOrd)

theorem badEnergies_nonempty
    (hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    (badEnergies hDensity hSob h0 hfree hret hefree heret hOrd).Nonempty := by
  obtain ⟨f, hf⟩ := hbad
  exact ⟨totalEnergy alpha f, f, hf, rfl⟩

theorem badEnergies_bddBelow (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) :
    BddBelow (badEnergies hDensity hSob h0 hfree hret hefree heret hOrd) := by
  refine ⟨0, ?_⟩
  rintro e ⟨f, hf, rfl⟩
  exact stable_energy_nonneg hOrd hH hS hf.1

theorem criticalLevel_le_bad_energy (hH : SharpOrdinaryHLS alpha)
    (hS : SharpOrdinarySobolev) {f : EnergyState}
    (hf : BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ≤ totalEnergy alpha f :=
  csInf_le (badEnergies_bddBelow hDensity hSob h0 hfree hret hefree heret hOrd hH hS)
    ⟨f, hf, rfl⟩

/-- The positive seed is the actual small-energy producer, not a new
induction premise.  Both nonempty and lower-bounded sInf domains are supplied. -/
theorem criticalLevel_pos_lt (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    0 < criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
      criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd <
        totalEnergy alpha (normalizedBubbleState alpha) := by
  obtain ⟨epsilon, hepsilon, M, hseed⟩ :=
    SmallEnergy.exists_positive_uniform_energy_seed hDensity hSob h0 hfree hret
      hefree heret hOrd hH hS S Bw Bs B6
  have hlower : epsilon ≤ criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd := by
    apply le_csInf (badEnergies_nonempty hDensity hSob h0 hfree hret hefree heret hOrd hbad)
    rintro e ⟨f, hf, rfl⟩
    by_contra hnot
    have hsmall : totalEnergy alpha f ≤ epsilon := (lt_of_not_ge hnot).le
    exact hf.2 ⟨M, hseed
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f)
      hf.1.1 hf.1.2 hsmall⟩
  obtain ⟨f, hf⟩ := hbad
  exact ⟨hepsilon.trans_le hlower,
    (criticalLevel_le_bad_energy hDensity hSob h0 hfree hret hefree heret hOrd hH hS hf).trans_lt
      hf.1.1⟩

/-- The strict lower-energy conclusion is individual. No common bound on the
scattering sizes of an entire sublevel is inferred from the infimum. -/
theorem finiteS_below_criticalLevel (hH : SharpOrdinaryHLS alpha)
    (hS : SharpOrdinarySobolev) {f : EnergyState} (hf : StableDatum alpha f)
    (he : totalEnergy alpha f < criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd) :
    FiniteSOnDomain (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f) := by
  by_contra hnot
  exact (not_lt_of_ge (criticalLevel_le_bad_energy hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS ⟨hf, hnot⟩)) he

theorem global_curveFinite_below_criticalLevel
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    {f : EnergyState} (hf : StableDatum alpha f)
    (he : totalEnergy alpha f < criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    U.domain = Set.univ ∧ CurveFinite U.state :=
  actualMaximalTrajectory_stable_global_curveFinite_of_finiteS
    hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6 0 f hf.1 hf.2
    (finiteS_below_criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd hH hS hf he)

/-- Translate the true time-zero lower-energy conclusion back to an arbitrary
mark; the exact maximal affine and finite-X frame bodies supply the transport. -/
theorem marked_global_curveFinite_below_criticalLevel
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (s : ℝ) {f : EnergyState} (hf : StableDatum alpha f)
    (he : totalEnergy alpha f < criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s f
    U.domain = Set.univ ∧ CurveFinite U.state :=
  actualMaximalTrajectory_marked_global_curveFinite hDensity hSob h0 hfree hret
    hefree heret hOrd s f
    (global_curveFinite_below_criticalLevel hDensity hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hf he)

/-- One fixed ceiling below W precedes every term of the minimizing sequence.
Its uniform gap, not closure of an open strict sublevel, controls extraction. -/
theorem exists_bad_minimizing_sequence
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    ∃ (Estar : ℝ) (u : ℕ → EnergyState),
      criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd < Estar ∧
      Estar < totalEnergy alpha (normalizedBubbleState alpha) ∧
      (∀ n, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd (u n)) ∧
      Tendsto (fun n => totalEnergy alpha (u n)) atTop
        (𝓝 (criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd)) ∧
      (∀ n, gradientSquared (u n) ≤ (2*(3+alpha)/(2+alpha))*totalEnergy alpha (u n)) ∧
      (∀ n, pureGradientNorm (u n) ≤ Real.sqrt ((2*(3+alpha)/(2+alpha))*Estar)) ∧
      (2*(3+alpha)/(2+alpha))*Estar < gradientSquared (normalizedBubbleState alpha) := by
  classical
  let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
  obtain ⟨_hEc, hEcW⟩ := criticalLevel_pos_lt hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 hbad
  obtain ⟨Estar, hEstar, hEstarW⟩ := exists_between hEcW
  have hne := badEnergies_nonempty hDensity hSob h0 hfree hret hefree heret hOrd hbad
  have choose_datum (n : ℕ) : ∃ f : EnergyState,
      BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f ∧
      totalEnergy alpha f < min Estar (Ec + 1/((n : ℝ)+1)) := by
    have hinv : 0 < 1/((n : ℝ)+1) := by positivity
    obtain ⟨e, ⟨f, hf, hfe⟩, he⟩ := exists_lt_of_csInf_lt hne
      (show Ec < min Estar (Ec+1/((n : ℝ)+1)) from
        lt_min hEstar (lt_add_of_pos_right Ec hinv))
    exact ⟨f, hf, hfe.trans_lt he⟩
  choose u hubad hu using choose_datum
  have hlo (n : ℕ) : Ec ≤ totalEnergy alpha (u n) :=
    criticalLevel_le_bad_energy hDensity hSob h0 hfree hret hefree heret hOrd hH hS (hubad n)
  have hupper (n : ℕ) : totalEnergy alpha (u n) ≤ Ec+1/((n : ℝ)+1) :=
    (hu n).le.trans (min_le_right _ _)
  have hd : Tendsto (fun n => totalEnergy alpha (u n)-Ec) atTop (𝓝 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (hlo n))
      (fun n => by linarith [hupper n]) tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun n => totalEnergy alpha (u n)) atTop (𝓝 Ec) := by
    simpa only [sub_add_cancel, zero_add] using hd.add_const Ec
  have hk := trapping_factor_pos hH
  have hgap : (2*(3+alpha)/(2+alpha))*Estar <
      gradientSquared (normalizedBubbleState alpha) := by
    rw [← trapping_factor_ground_energy hDensity hOrd hH hS]
    exact mul_lt_mul_of_pos_left hEstarW hk
  refine ⟨Estar, u, hEstar, hEstarW, hubad, ht,
    (fun n => stable_kinetic_le_energy hOrd hH hS (hubad n).1), ?_, hgap⟩
  intro n
  apply pureGradientNorm_le_of_gradientSquared_le
  exact (stable_kinetic_le_energy hOrd hH hS (hubad n).1).trans
    (mul_le_mul_of_nonneg_left ((hu n).le.trans (min_le_left _ _)) hk.le)

end HartreeF.ActualCriticalThreshold
