import FActualSIntervalBounds
import FActualBalancedGraphWindows
import FActualSpatialBadTransport

/-! Badness survives arbitrary native time recentering and spatial normalization.
The finite-S argument retains the compact bridge between the two marks. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualRecenterBadTransport
open EnergySpace CriticalPathSpace CriticalSourceBounds MaximalTrajectory CriticalAffine
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open BilateralPathTools BilateralWindows BilateralSideStability LinearWeakEquation
open ActualSIntervalBounds ActualSpatialBadTransport
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  actualMaximalTrajectory LocalMildTrajectory.path

private theorem finite_after_of_translated_graph_cap
    (hDensity : OrdinaryH1Density) {K alpha kernel c R : ℝ} (hSob : OrdinarySobolev K)
    {f g : EnergyState} (M : LocalMildTrajectory alpha kernel 0 f)
    (U : LocalMildTrajectory alpha kernel 0 g) (hc : c ∈ M.domain)
    (heq : EqOn U.state (fun t => M.state (c+t)) U.domain)
    (hR : 0 ≤ R) (hdom : Ici 0 ⊆ U.domain)
    (hcap : ∀ (b : ℝ) (hb : 0 ≤ b) (hI : Icc 0 b ⊆ U.domain), ‖U.path hb hI‖ ≤ R) :
    ActualScattering.FiniteSAfter M := by
  let d := max 0 c
  have hd : 0 ≤ d := le_max_left _ _
  have hcd : c ≤ d := le_max_right _ _
  have hdM : d ∈ M.domain := by
    rcases le_total 0 c with h | h
    · simpa only [d, max_eq_right h] using hc
    · simpa only [d, max_eq_left h] using M.center_mem
  have hJ : Icc 0 d ⊆ M.domain := M.domain_connected.out' M.center_mem hdM
  let L : ℝ≥0 := ⟨graphSConstant K * ‖M.path hd hJ‖,
    mul_nonneg (graphSConstant_nonneg hSob) (norm_nonneg _)⟩
  let H : ℝ≥0 := ⟨graphSConstant K * R, mul_nonneg (graphSConstant_nonneg hSob) hR⟩
  have hL : pathValueSize (intervalMeasure 0 d) (M.path hd hJ) ≤ (L : ℝ≥0∞) :=
    (pathValueSize_le_graph hDensity hSob _).trans_eq
      (show ENNReal.ofReal (L : ℝ) = (L : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
  have htail (b : ℝ) (hcb : c ≤ b) (hMc : Icc c b ⊆ M.domain) :
      pathValueSize (intervalMeasure c b) (M.path hcb hMc) ≤ (H : ℝ≥0∞) := by
    have hV : Icc (c-c) (b-c) ⊆ U.domain := by
      intro t ht
      apply hdom
      simpa only [sub_self] using ht.1
    have hV0 : Icc 0 (b-c) ⊆ U.domain := fun _ ht => hdom ht.1
    have hn := translated_path_norm M U c heq hcb hMc hV
    have hbound : ‖U.path (sub_le_sub_right hcb c) hV‖ ≤ R := by
      simpa only [sub_self] using hcap (b-c) (sub_nonneg.mpr hcb) hV0
    have hgraph : ‖M.path hcb hMc‖ ≤ R := hn.symm.le.trans hbound
    exact ((pathValueSize_le_graph hDensity hSob _).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hgraph
        (graphSConstant_nonneg hSob)))).trans_eq
          (show ENNReal.ofReal (H : ℝ) = (H : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
  refine ⟨L+H, ?_⟩
  intro b hb hI
  rw [ENNReal.coe_add]
  by_cases hbd : b ≤ d
  · exact ((actual_snorm_mono hDensity hSob M hd hJ le_rfl hb hbd hI).trans hL).trans
      (le_self_add)
  · have hdb : d ≤ b := (lt_of_not_ge hbd).le
    have hbM : b ∈ M.domain := hI ⟨hb, le_rfl⟩
    have hMc : Icc c b ⊆ M.domain := M.domain_connected.out' hc hbM
    have hMd : Icc d b ⊆ M.domain := M.domain_connected.out' hdM hbM
    have hT := (actual_snorm_mono hDensity hSob M (hcd.trans hdb) hMc hcd hdb le_rfl hMd).trans
      (htail b (hcd.trans hdb) hMc)
    exact (actual_snorm_split_le hDensity hSob M hd hdb hI hJ hMd).trans (add_le_add hL hT)

private theorem finite_before_of_translated_graph_cap
    (hDensity : OrdinaryH1Density) {K alpha kernel c R : ℝ} (hSob : OrdinarySobolev K)
    {f g : EnergyState} (M : LocalMildTrajectory alpha kernel 0 f)
    (U : LocalMildTrajectory alpha kernel 0 g) (hc : c ∈ M.domain)
    (heq : EqOn U.state (fun t => M.state (c+t)) U.domain)
    (hR : 0 ≤ R) (hdom : Iic 0 ⊆ U.domain)
    (hcap : ∀ (b : ℝ) (hb : b ≤ 0) (hI : Icc b 0 ⊆ U.domain), ‖U.path hb hI‖ ≤ R) :
    ActualLeftScattering.FiniteSBefore M := by
  let d := min 0 c
  have hd : d ≤ 0 := min_le_left _ _
  have hdc : d ≤ c := min_le_right _ _
  have hdM : d ∈ M.domain := by
    rcases le_total 0 c with h | h
    · simpa only [d, min_eq_left h] using M.center_mem
    · simpa only [d, min_eq_right h] using hc
  have hJ : Icc d 0 ⊆ M.domain := M.domain_connected.out' hdM M.center_mem
  let L : ℝ≥0 := ⟨graphSConstant K * ‖M.path hd hJ‖,
    mul_nonneg (graphSConstant_nonneg hSob) (norm_nonneg _)⟩
  let H : ℝ≥0 := ⟨graphSConstant K * R, mul_nonneg (graphSConstant_nonneg hSob) hR⟩
  have hL : pathValueSize (intervalMeasure d 0) (M.path hd hJ) ≤ (L : ℝ≥0∞) :=
    (pathValueSize_le_graph hDensity hSob _).trans_eq
      (show ENNReal.ofReal (L : ℝ) = (L : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
  have htail (b : ℝ) (hbc : b ≤ c) (hMc : Icc b c ⊆ M.domain) :
      pathValueSize (intervalMeasure b c) (M.path hbc hMc) ≤ (H : ℝ≥0∞) := by
    have hV : Icc (b-c) (c-c) ⊆ U.domain := by
      intro t ht
      apply hdom
      simpa only [sub_self] using ht.2
    have hV0 : Icc (b-c) 0 ⊆ U.domain := fun _ ht => hdom ht.2
    have hn := translated_path_norm M U c heq hbc hMc hV
    have hbound : ‖U.path (sub_le_sub_right hbc c) hV‖ ≤ R := by
      simpa only [sub_self] using hcap (b-c) (sub_nonpos.mpr hbc) hV0
    have hgraph : ‖M.path hbc hMc‖ ≤ R := hn.symm.le.trans hbound
    exact ((pathValueSize_le_graph hDensity hSob _).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hgraph
        (graphSConstant_nonneg hSob)))).trans_eq
          (show ENNReal.ofReal (H : ℝ) = (H : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
  refine ⟨H+L, ?_⟩
  intro b hb hI
  rw [ENNReal.coe_add]
  by_cases hdb : d ≤ b
  · exact ((actual_snorm_mono hDensity hSob M hd hJ hdb hb le_rfl hI).trans hL).trans
      (le_add_self)
  · have hbd : b ≤ d := (lt_of_not_ge hdb).le
    have hbM : b ∈ M.domain := hI ⟨le_rfl, hb⟩
    have hMc : Icc b c ⊆ M.domain := M.domain_connected.out' hbM hc
    have hMd : Icc b d ⊆ M.domain := M.domain_connected.out' hbM hdM
    have hT := (actual_snorm_mono hDensity hSob M (hbd.trans hdc) hMc le_rfl hbd hdc hMd).trans
      (htail b (hbd.trans hdc) hMc)
    exact (actual_snorm_split_le hDensity hSob M hbd hd hI hMd hJ).trans (add_le_add hT hL)

/-- Native gradient bounds are transported on exactly the translated domain. -/
theorem zero_recenter_gradient_cap
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (f : EnergyState) (c : ℝ) (hc : c ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain)
    (hgradient : ∀ t ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain,
      pureGradientNorm ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).state t) ≤ B) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (M.state c)
    ∀ t ∈ U.domain, pureGradientNorm (U.state t) ≤ B := by
  intro M U t ht
  have hcov := actualMaximalTrajectory_zero_recenter hDensity hSob h0 hfree hret hefree heret hH f hc
  have htM : c+t ∈ M.domain := by
    change t ∈ (fun s : ℝ => c+s) ⁻¹' M.domain
    rw [← hcov.1]
    exact ht
  have he : U.state t = M.state (c+t) := hcov.2 ht
  rw [he]
  exact hgradient _ htM

/-- Badness in this time direction survives every native recentering. -/
theorem forward_bad_of_zero_recenter
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (f : EnergyState) (c : ℝ) (hc : c ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain)
    (hgradient : ∀ t ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain,
      pureGradientNorm ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).state t) ≤ B) (hB : 0 ≤ B)
    (hbad : ¬ ActualScattering.FiniteSAfter (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f)) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f
    ¬ ActualScattering.FiniteSAfter (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (M.state c)) := by
  intro M hfinite
  let z := M.state c
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 z
  have hgrad := zero_recenter_gradient_cap hDensity hSob h0 hfree hret hefree heret hH f c hc hgradient
  have hz : Tendsto (fun _ : ℕ => ‖z-z‖) atTop (𝓝 0) := by
    simp only [sub_self, norm_zero]
    exact tendsto_const_nhds
  obtain ⟨R, hR, N, hcap⟩ := exists_eventual_forward_graph_cap_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique z hB hgrad hfinite (fun _ => z) hz
  obtain ⟨hdom, hgraph⟩ := hcap N le_rfl
  have hcov := actualMaximalTrajectory_zero_recenter hDensity hSob h0 hfree hret hefree heret hH f hc
  exact hbad (finite_after_of_translated_graph_cap hDensity hSob M U hc hcov.2 hR hdom hgraph)

/-- Badness in this time direction survives every native recentering. -/
theorem backward_bad_of_zero_recenter
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (f : EnergyState) (c : ℝ) (hc : c ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain)
    (hgradient : ∀ t ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain,
      pureGradientNorm ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).state t) ≤ B) (hB : 0 ≤ B)
    (hbad : ¬ ActualLeftScattering.FiniteSBefore (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f)) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f
    ¬ ActualLeftScattering.FiniteSBefore (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (M.state c)) := by
  intro M hfinite
  let z := M.state c
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 z
  have hgrad := zero_recenter_gradient_cap hDensity hSob h0 hfree hret hefree heret hH f c hc hgradient
  have hz : Tendsto (fun _ : ℕ => ‖z-z‖) atTop (𝓝 0) := by
    simp only [sub_self, norm_zero]
    exact tendsto_const_nhds
  obtain ⟨R, hR, N, hcap⟩ := exists_eventual_backward_graph_cap_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique z hB hgrad hfinite (fun _ => z) hz
  obtain ⟨hdom, hgraph⟩ := hcap N le_rfl
  have hcov := actualMaximalTrajectory_zero_recenter hDensity hSob h0 hfree hret hefree heret hH f hc
  exact hbad (finite_before_of_translated_graph_cap hDensity hSob M U hc hcov.2 hR hdom hgraph)

/-- Both bad directions of the original trajectory survive arbitrary native
time sampling and positive spatial normalization. -/
theorem normalized_bilateral_bad
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (f : EnergyState) (c : ℝ) (hc : c ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain)
    (hgradient : ∀ t ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain,
      pureGradientNorm ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).state t) ≤ B) (hB : 0 ≤ B)
    {r : ℝ} (hr : 0 < r) (y : Space)
    (hfuture : ¬ ActualScattering.FiniteSAfter (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f))
    (hpast : ¬ ActualLeftScattering.FiniteSBefore (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f)) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f
    let z := (criticalAffineState r hr y).symm (M.state c)
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 z
    (¬ ActualScattering.FiniteSAfter U) ∧ (¬ ActualLeftScattering.FiniteSBefore U) := by
  intro M z U
  have hgrad := zero_recenter_gradient_cap hDensity hSob h0 hfree hret hefree heret hH f c hc hgradient
  have hf := forward_bad_of_zero_recenter hDensity hSob h0 hfree hret hefree heret hH hgen hUnique f c hc hgradient hB hfuture
  have hp := backward_bad_of_zero_recenter hDensity hSob h0 hfree hret hefree heret hH hgen hUnique f c hc hgradient hB hpast
  exact ⟨forward_bad_of_spatial_normalization hDensity hSob h0 hfree hret hefree heret hH hgen hUnique (M.state c) hr y hB hgrad hf,
    backward_bad_of_spatial_normalization hDensity hSob h0 hfree hret hefree heret hH hgen hUnique (M.state c) hr y hB hgrad hp⟩

end HartreeF.ActualRecenterBadTransport
