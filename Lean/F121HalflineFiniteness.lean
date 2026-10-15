import F121ActualValueDomain
import FActualCoherentPathValueExhaustion
import FCompactLpExhaustion

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121Finiteness
open EnergySpace CriticalPathSpace MaximalTrajectory SobolevStretch StationarySelfTest
  IntervalNormExhaustion Paper121ActualNorm Paper121ActualDomain Paper121Halfline

theorem actual_after_bound (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (M : ℝ≥0)
    (hM : ActualSTail.UniformSNormAfter U s M) :
    TimeHolder.mixedNorm (volume.restrict (U.domain ∩ Ici s)) volume 10 10
      (fun t => energyValue (U.state t)) ≤ (M : ℝ≥0∞) := by
  obtain ⟨b, hb, hbI, hcover⟩ :=
    exists_right_interval_exhaustion U.domain U.domain_connected U.center_mem
  have hI (n : ℕ) : Icc s (b n) ⊆ U.domain :=
    U.domain_connected.out' U.center_mem (hbI n).1
  obtain ⟨F, hFM, hF, _⟩ := exists_actual_global_value_of_coherent_paths
    hDensity hSob M.property (fun _ => s) b (fun _ _ _ => le_rfl) hb
    (fun n => (hbI n).2) U.state (fun n => U.path (hbI n).2 (hI n))
    (fun n => U.path_agrees (hbI n).2 (hI n))
    (fun n => by simpa only [ENNReal.ofReal_coe_nnreal] using hM (b n) (hbI n).2 (hI n))
  have h := actual_mixedNorm_le_of_global_nestedLp volume 10 10 _ F
    (fun t => energyValue (U.state t)) hFM hF
  simpa only [hcover, ENNReal.ofReal_coe_nnreal] using h

theorem actual_before_bound (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (M : ℝ≥0)
    (hM : ActualInfiniteLeftSTail.UniformSNormBefore U s M) :
    TimeHolder.mixedNorm (volume.restrict (U.domain ∩ Iic s)) volume 10 10
      (fun t => energyValue (U.state t)) ≤ (M : ℝ≥0∞) := by
  obtain ⟨a, ha, haI, hcover⟩ :=
    exists_left_interval_exhaustion U.domain U.domain_connected U.center_mem
  have hI (n : ℕ) : Icc (a n) s ⊆ U.domain :=
    U.domain_connected.out' (haI n).1 U.center_mem
  obtain ⟨F, hFM, hF, _⟩ := exists_actual_global_value_of_coherent_paths
    hDensity hSob M.property a (fun _ => s) ha (fun _ _ _ => le_rfl)
    (fun n => (haI n).2) U.state (fun n => U.path (haI n).2 (hI n))
    (fun n => U.path_agrees (haI n).2 (hI n))
    (fun n => by simpa only [ENNReal.ofReal_coe_nnreal] using hM (a n) (haI n).2 (hI n))
  have h := actual_mixedNorm_le_of_global_nestedLp volume 10 10 _ F
    (fun t => energyValue (U.state t)) hFM hF
  simpa only [hcover, ENNReal.ofReal_coe_nnreal] using h

theorem finite_after_iff_literal (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) :
    ActualScattering.FiniteSAfter U ↔
      TimeHolder.mixedNorm (volume.restrict (U.domain ∩ Ici s)) volume 10 10
        (fun t => energyValue (U.state t)) ≠ ∞ := by
  constructor
  · rintro ⟨M, hM⟩
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (actual_after_bound hDensity hSob U M hM)
  · intro h
    let L := TimeHolder.mixedNorm (volume.restrict (U.domain ∩ Ici s)) volume 10 10
      (fun t => energyValue (U.state t))
    have hn : nativeSAfter U s ≤ L := by
      dsimp only [L]
      rw [actual_mixedNorm_eq_value_norm hDensity hSob U _ inter_subset_left]
      exact nativeSAfter_le_actual_halfline_norm hDensity hSob U s
    refine ⟨L.toNNReal, ?_⟩
    intro b hab hI
    rw [ENNReal.coe_toNNReal h]
    exact (le_iSup_of_le b (le_iSup_of_le hab (le_iSup_of_le hI le_rfl))).trans hn

theorem finite_before_iff_literal (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) :
    ActualLeftScattering.FiniteSBefore U ↔
      TimeHolder.mixedNorm (volume.restrict (U.domain ∩ Iic s)) volume 10 10
        (fun t => energyValue (U.state t)) ≠ ∞ := by
  constructor
  · rintro ⟨M, hM⟩
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (actual_before_bound hDensity hSob U M hM)
  · intro h
    let L := TimeHolder.mixedNorm (volume.restrict (U.domain ∩ Iic s)) volume 10 10
      (fun t => energyValue (U.state t))
    have hn : nativeSBefore U s ≤ L := by
      dsimp only [L]
      rw [actual_mixedNorm_eq_value_norm hDensity hSob U _ inter_subset_left]
      exact nativeSBefore_le_actual_halfline_norm hDensity hSob U s
    refine ⟨L.toNNReal, ?_⟩
    intro b hba hI
    rw [ENNReal.coe_toNNReal h]
    exact (le_iSup_of_le b (le_iSup_of_le hba (le_iSup_of_le hI le_rfl))).trans hn

end HartreeF.Paper121Finiteness
