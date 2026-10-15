import FOriginalCriticalSequenceWindows
import FStateSharpThresholdReviewConsumers

/-! Hartree v23 Lemma 2.16: sequences at the ORIGINAL uniform threshold.
The selected time centers lie in finite native windows. No datum is assumed
individually nonscattering. Time-zero recentering remains to be assembled. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.OriginalUniformSequence
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz ActualCriticalThreshold
  OriginalUniformThreshold OriginalCriticalWindows CriticalPathSpace CriticalSourceBounds
  CriticalPathRestriction BilateralPathTools

/-- Two large actual S paths on one native finite window. -/
structure NativeSWindow {alpha kernel s : ℝ} {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (T : ℝ) where
  left : ℝ
  center : ℝ
  right : ℝ
  left_lt : left < center
  right_lt : center < right
  within : Icc left right ⊆ U.domain
  left_large : ENNReal.ofReal T < pathValueSize (intervalMeasure left center)
    (U.path left_lt.le (fun _ ht => within ⟨ht.1, ht.2.trans right_lt.le⟩))
  right_large : ENNReal.ofReal T < pathValueSize (intervalMeasure center right)
    (U.path right_lt.le (fun _ ht => within ⟨left_lt.le.trans ht.1, ht.2⟩))

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))

theorem exists_native_S_window {E T : ℝ}
    (hE : uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd < E)
    (hEW : E < totalEnergy alpha (normalizedBubbleState alpha)) (hT : 0 < T) :
    ∃ f : EnergyState, StableDatum alpha f ∧ totalEnergy alpha f ≤ E ∧
      Nonempty (NativeSWindow
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f) T) := by
  obtain ⟨f, hf, he, a, b, hab, hI, c, hac, hcb, hL, hR⟩ :=
    exists_balanced_native_window hDensity hSob h0 hfree hret hefree heret hOrd hE hEW hT
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
  refine ⟨f, hf, he, ⟨⟨a, c, b, hac, hcb, hI, ?_, ?_⟩⟩⟩
  · rw [path_restrict U hab hI le_rfl hac.le hcb.le]
    exact hL
  · rw [path_restrict U hab hI hac.le hcb.le le_rfl]
    exact hR

/-- Actual stable data approach the uniform critical energy, with a common
strict energy ceiling and two S-large windows about one center per datum. -/
theorem exists_uniform_critical_window_sequence
    (hne : (uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd).Nonempty)
    (hEcW : uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd <
      totalEnergy alpha (normalizedBubbleState alpha)) :
    ∃ (Estar : ℝ) (u : ℕ → EnergyState),
      uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd < Estar ∧
      Estar < totalEnergy alpha (normalizedBubbleState alpha) ∧
      (∀ n, StableDatum alpha (u n)) ∧
      (∀ n, totalEnergy alpha (u n) ≤ Estar) ∧
      Tendsto (fun n => totalEnergy alpha (u n)) atTop
        (𝓝 (uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd)) ∧
      ∀ n, Nonempty (NativeSWindow
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (u n))
        ((n : ℝ)+1)) := by
  classical
  let Ec := uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
  obtain ⟨Estar, hstar, hstarW⟩ := exists_between hEcW
  let ceiling : ℕ → ℝ := fun n => min Estar (Ec + 1/((n : ℝ)+1))
  have hceil (n : ℕ) : Ec < ceiling n := lt_min hstar (lt_add_of_pos_right Ec (by positivity))
  have hceilW (n : ℕ) : ceiling n < totalEnergy alpha (normalizedBubbleState alpha) :=
    (min_le_left _ _).trans_lt hstarW
  have hchoice (n : ℕ) := exists_native_S_window hDensity hSob h0 hfree hret hefree heret
    hOrd (hceil n) (hceilW n) (by positivity : 0 < (n : ℝ)+1)
  choose u hu he hw using hchoice
  have hdiff : Tendsto (fun n => ceiling n-Ec) atTop (𝓝 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (hceil n).le)
      (fun n => by have h := min_le_right Estar (Ec + 1/((n : ℝ)+1)); dsimp [ceiling]; linarith)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto ceiling atTop (𝓝 Ec) := by
    simpa only [sub_add_cancel, zero_add] using hdiff.add_const Ec
  have hescape (n : ℕ) : ¬ UniformCompactS
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (u n))
      (n : ℝ≥0) := by
    intro hcap
    obtain ⟨w⟩ := hw n
    have hbound := hcap w.left w.center w.left_lt.le
      (fun _ ht => w.within ⟨ht.1, ht.2.trans w.right_lt.le⟩)
    have hn : (n : ℝ≥0∞) ≤ ENNReal.ofReal ((n : ℝ)+1) := by
      simpa using ENNReal.ofReal_le_ofReal (show (n : ℝ) ≤ (n : ℝ)+1 by linarith)
    exact (not_le_of_gt w.left_large) (hbound.trans hn)
  refine ⟨Estar, u, hstar, hstarW, hu, (fun n => (he n).trans (min_le_left _ _)), ?_, hw⟩
  exact escaping_bounds_energy_tendsto hDensity hSob h0 hfree hret hefree heret hOrd
    hne u ceiling hu he hlim hescape

/-- Original uniform-failure premise suffices for a positive critical level.
Existence of an individually nonscattering datum is NOT assumed. -/
theorem uniform_threshold_bounds_of_failure
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    {E0 : ℝ} (hE0 : E0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hfailure : ¬ UniformSBelow hDensity hSob h0 hfree hret hefree heret hOrd E0) :
    (uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd).Nonempty ∧
    0 < uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
    uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ≤ E0 ∧
    E0 < totalEnergy alpha (normalizedBubbleState alpha) := by
  have hW : 0 < totalEnergy alpha (normalizedBubbleState alpha) := by
    have h := (StateSharpThresholdReview.canonical_zero_strictly_below_W hOrd hH hS hDensity).2
    simpa only [StateSharpThresholdReview.canonical_zero_energy hH.order_pos] using h
  obtain ⟨eps, heps, R, hseed⟩ := SmallEnergy.exists_positive_uniform_energy_seed
    hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6
  let e := min eps (totalEnergy alpha (normalizedBubbleState alpha)/2)
  have hep : 0 < e := lt_min heps (half_pos hW)
  have hem : e ∈ uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd := by
    refine ⟨(min_le_right _ _).trans_lt (half_lt_self hW), R, ?_⟩
    intro f hf he
    exact hseed (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f)
      hf.1 hf.2 (he.trans (min_le_left _ _))
  have hne : (uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd).Nonempty := ⟨e, hem⟩
  refine ⟨hne, hep.trans_le (le_csSup
    (uniformEnergies_bddAbove hDensity hSob h0 hfree hret hefree heret hOrd) hem), ?_, hE0⟩
  by_contra hnot
  exact hfailure (uniformSBelow_of_lt hDensity hSob h0 hfree hret hefree heret hOrd
    hne (lt_of_not_ge hnot))

/-- Original Lemma 2.16 input, with all sequence witnesses constructed.
The finite-window centers are exposed; zero-mark recentering is still pending. -/
theorem exists_uniform_sequence_of_failure
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    {E0 : ℝ} (hE0 : E0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hfailure : ¬ UniformSBelow hDensity hSob h0 hfree hret hefree heret hOrd E0) :
    0 < uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
    ∃ (Estar : ℝ) (u : ℕ → EnergyState),
      uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd < Estar ∧
      Estar < totalEnergy alpha (normalizedBubbleState alpha) ∧
      (∀ n, StableDatum alpha (u n)) ∧
      (∀ n, totalEnergy alpha (u n) ≤ Estar) ∧
      Tendsto (fun n => totalEnergy alpha (u n)) atTop
        (𝓝 (uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd)) ∧
      ∀ n, Nonempty (NativeSWindow
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (u n))
        ((n : ℝ)+1)) := by
  obtain ⟨hne, hpos, hle, hupper⟩ := uniform_threshold_bounds_of_failure
    hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6 hE0 hfailure
  exact ⟨hpos, exists_uniform_critical_window_sequence
    hDensity hSob h0 hfree hret hefree heret hOrd hne (hle.trans_lt hupper)⟩

end HartreeF.OriginalUniformSequence
