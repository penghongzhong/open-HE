import FActualBilateralCriticalProfile
import FPartitionGlobalGraphBound

/-! Arbitrary prescribed native time centers on the same actual critical orbit.
The two-piece graph estimate uses a literal count-two partition. No center is
reselected, no outside-domain state identity is used, and no global lifespan is
claimed. Source-only draft: UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualNativeOrbitWindows
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW
  LocalRellich LinearWeakEquation CriticalPathSpace
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace

private theorem native_path_norm_restrict {alpha kernel s a b c d : ℝ}
    {f : EnergyState} (U : LocalMildTrajectory alpha kernel s f)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hAB : Icc a b ⊆ U.domain) (hCD : Icc c d ⊆ U.domain) :
    ‖U.path hcd hCD‖ ≤ ‖U.path (hac.trans (hcd.trans hdb)) hAB‖ := by
  rw [BilateralPathTools.path_restrict U (hac.trans (hcd.trans hdb)) hAB hac hcd hdb hCD]
  exact CriticalPathRestriction.restrictPath_norm_le hac hcd hdb _

/-- Degenerate pieces remain genuine graph paths; their norms are not set to zero. -/
private theorem native_path_norm_two_piece {alpha kernel s a c b : ℝ}
    {f : EnergyState} (U : LocalMildTrajectory alpha kernel s f)
    (hac : a ≤ c) (hcb : c ≤ b) (hAB : Icc a b ⊆ U.domain)
    (hAC : Icc a c ⊆ U.domain) (hCB : Icc c b ⊆ U.domain) :
    ‖U.path (hac.trans hcb) hAB‖ ≤
      2 * max ‖U.path hac hAC‖ ‖U.path hcb hCB‖ := by
  classical
  let nodes : Fin 3 → ℝ := fun i => if i = 0 then a else if i = 1 then c else b
  have hnodes : Monotone nodes := by
    have hab := hac.trans hcb
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [nodes]
  let P : TimePartition.Partition a b :=
    ⟨2, by decide, nodes, by simp [nodes], by simp [nodes], hnodes⟩
  let q := U.path (hac.trans hcb) hAB
  let G := max ‖U.path hac hAC‖ ‖U.path hcb hCB‖
  have hG : 0 ≤ G := (norm_nonneg _).trans (le_max_left _ _)
  have hp : ∀ i : Fin P.count, ‖ActualPathPartitions.piecePath P q i‖ ≤ G := by
    intro i
    change Fin 2 at i
    fin_cases i
    · change ‖CriticalPathRestriction.restrictPath le_rfl hac hcb
        (U.path (hac.trans hcb) hAB)‖ ≤ G
      rw [← BilateralPathTools.path_restrict U (hac.trans hcb) hAB
        le_rfl hac hcb hAC]
      exact le_max_left _ _
    · change ‖CriticalPathRestriction.restrictPath hac hcb le_rfl
        (U.path (hac.trans hcb) hAB)‖ ≤ G
      rw [← BilateralPathTools.path_restrict U (hac.trans hcb) hAB
        hac hcb le_rfl hCB]
      exact le_max_right _ _
  simpa only [P, Nat.cast_ofNat, q, G] using
    FinitePerturbation.global_graph_norm_le_piece_bound (hac.trans hcb) P q hG hp

private theorem finiteSAfter_of_native_graph_cap (hDensity : OrdinaryH1Density)
    {K alpha kernel Q : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (V : LocalMildTrajectory alpha kernel 0 f) (hQ : 0 ≤ Q)
    (hcap : ∀ (b : ℝ) (hb : 0 ≤ b) (hI : Icc 0 b ⊆ V.domain),
      ‖V.path hb hI‖ ≤ Q) : ActualScattering.FiniteSAfter V := by
  let C := BilateralPathTools.graphSConstant K
  have hC : 0 ≤ C := BilateralPathTools.graphSConstant_nonneg hSob
  refine ⟨⟨C * Q, mul_nonneg hC hQ⟩, ?_⟩
  intro b hb hI
  have h : CriticalSourceBounds.pathValueSize (intervalMeasure 0 b) (V.path hb hI) ≤
      ENNReal.ofReal (C * Q) :=
    (BilateralPathTools.pathValueSize_le_graph hDensity hSob (V.path hb hI)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcap b hb hI) hC))
  simpa only [ENNReal.ofReal_eq_coe_nnreal (mul_nonneg hC hQ)] using h

private theorem finiteSBefore_of_native_graph_cap (hDensity : OrdinaryH1Density)
    {K alpha kernel Q : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (V : LocalMildTrajectory alpha kernel 0 f) (hQ : 0 ≤ Q)
    (hcap : ∀ (a : ℝ) (ha : a ≤ 0) (hI : Icc a 0 ⊆ V.domain),
      ‖V.path ha hI‖ ≤ Q) : ActualLeftScattering.FiniteSBefore V := by
  let C := BilateralPathTools.graphSConstant K
  have hC : 0 ≤ C := BilateralPathTools.graphSConstant_nonneg hSob
  refine ⟨⟨C * Q, mul_nonneg hC hQ⟩, ?_⟩
  intro a ha hI
  have h : CriticalSourceBounds.pathValueSize (intervalMeasure a 0) (V.path ha hI) ≤
      ENNReal.ofReal (C * Q) :=
    (BilateralPathTools.pathValueSize_le_graph hDensity hSob (V.path ha hI)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcap a ha hI) hC))
  simpa only [ENNReal.ofReal_eq_coe_nnreal (mul_nonneg hC hQ)] using h

/-- The center is arbitrary in the native domain, including either side of zero. -/
theorem native_forward_graph_unbounded (hDensity : OrdinaryH1Density)
    {K alpha kernel : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (V : LocalMildTrajectory alpha kernel 0 f)
    (hfuture : ¬ ActualScattering.FiniteSAfter V)
    (c : ℝ) (hc : c ∈ V.domain) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (b : ℝ) (hcb : c ≤ b) (hI : Icc c b ⊆ V.domain),
      R < ‖V.path hcb hI‖ := by
  by_contra hn
  have hcap : ∀ (b : ℝ) (hcb : c ≤ b) (hI : Icc c b ⊆ V.domain),
      ‖V.path hcb hI‖ ≤ R := by
    intro b hcb hI
    exact le_of_not_gt (fun hlt => hn ⟨b, hcb, hI, hlt⟩)
  apply hfuture
  by_cases hc0 : c ≤ 0
  · apply finiteSAfter_of_native_graph_cap hDensity hSob V hR
    intro b hb hI
    have hbV : b ∈ V.domain := hI ⟨hb, le_rfl⟩
    have hcbI : Icc c b ⊆ V.domain := V.domain_connected.out' hc hbV
    exact (native_path_norm_restrict V hc0 hb le_rfl hcbI hI).trans
      (hcap b (hc0.trans hb) hcbI)
  · have h0c : 0 ≤ c := (lt_of_not_ge hc0).le
    have hbridge : Icc 0 c ⊆ V.domain := V.domain_connected.out' V.center_mem hc
    let B := ‖V.path h0c hbridge‖
    have hM : 0 ≤ max B R := (norm_nonneg _).trans (le_max_left _ _)
    apply finiteSAfter_of_native_graph_cap (Q := 2 * max B R) hDensity hSob V
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
    intro b hb hI
    by_cases hbc : b ≤ c
    · have hbB : ‖V.path hb hI‖ ≤ B :=
        native_path_norm_restrict V le_rfl hb hbc hbridge hI
      have hBM : B ≤ max B R := le_max_left _ _
      linarith
    · have hcb : c ≤ b := (lt_of_not_ge hbc).le
      have hbV : b ∈ V.domain := hI ⟨hb, le_rfl⟩
      have hcbI : Icc c b ⊆ V.domain := V.domain_connected.out' hc hbV
      exact (native_path_norm_two_piece V h0c hcb hI hbridge hcbI).trans
        (mul_le_mul_of_nonneg_left (max_le_max le_rfl (hcap b hcb hcbI))
          (by norm_num : (0 : ℝ) ≤ 2))

/-- The reversed endpoint-order proof still uses forward-oriented compact paths. -/
theorem native_backward_graph_unbounded (hDensity : OrdinaryH1Density)
    {K alpha kernel : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (V : LocalMildTrajectory alpha kernel 0 f)
    (hpast : ¬ ActualLeftScattering.FiniteSBefore V)
    (c : ℝ) (hc : c ∈ V.domain) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (a : ℝ) (hac : a ≤ c) (hI : Icc a c ⊆ V.domain),
      R < ‖V.path hac hI‖ := by
  by_contra hn
  have hcap : ∀ (a : ℝ) (hac : a ≤ c) (hI : Icc a c ⊆ V.domain),
      ‖V.path hac hI‖ ≤ R := by
    intro a hac hI
    exact le_of_not_gt (fun hlt => hn ⟨a, hac, hI, hlt⟩)
  apply hpast
  by_cases h0c : 0 ≤ c
  · apply finiteSBefore_of_native_graph_cap hDensity hSob V hR
    intro a ha hI
    have haV : a ∈ V.domain := hI ⟨le_rfl, ha⟩
    have hacI : Icc a c ⊆ V.domain := V.domain_connected.out' haV hc
    exact (native_path_norm_restrict V le_rfl ha h0c hacI hI).trans
      (hcap a (ha.trans h0c) hacI)
  · have hc0 : c ≤ 0 := (lt_of_not_ge h0c).le
    have hbridge : Icc c 0 ⊆ V.domain := V.domain_connected.out' hc V.center_mem
    let B := ‖V.path hc0 hbridge‖
    have hM : 0 ≤ max R B := (norm_nonneg _).trans (le_max_right _ _)
    apply finiteSBefore_of_native_graph_cap (Q := 2 * max R B) hDensity hSob V
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
    intro a ha hI
    by_cases hca : c ≤ a
    · have haB : ‖V.path ha hI‖ ≤ B :=
        native_path_norm_restrict V hca ha le_rfl hbridge hI
      have hBM : B ≤ max R B := le_max_right _ _
      linarith
    · have hac : a ≤ c := (lt_of_not_ge hca).le
      have haV : a ∈ V.domain := hI ⟨le_rfl, ha⟩
      have hacI : Icc a c ⊆ V.domain := V.domain_connected.out' haV hc
      exact (native_path_norm_two_piece V hac hc0 hI hacI hbridge).trans
        (mul_le_mul_of_nonneg_left (max_le_max (hcap a hac hacI) le_rfl)
          (by norm_num : (0 : ℝ) ≤ 2))

/-- Actual recentering of the prescribed state, with both graph norms transported
without changing the original physical center. -/
theorem prescribed_center_bilateral_windows (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (psi : EnergyState)
    (hfuture : ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi))
    (hpast : ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi))
    (c : ℝ)
    (hc : c ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).domain)
    (R : ℝ) (hR : 0 ≤ R) :
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (V.state c)
    ∃ (a b : ℝ) (ha : a ≤ 0) (hb : 0 ≤ b)
      (hL : Icc a 0 ⊆ U.domain) (hRight : Icc 0 b ⊆ U.domain),
      R < ‖U.path ha hL‖ ∧ R < ‖U.path hb hRight‖ := by
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (V.state c)
  obtain ⟨a, hac, hAI, hlargeL⟩ :=
    native_backward_graph_unbounded hDensity hSob V hpast c hc R hR
  obtain ⟨b, hcb, hBI, hlargeR⟩ :=
    native_forward_graph_unbounded hDensity hSob V hfuture c hc R hR
  have hcenter := BilateralPathTools.actualMaximalTrajectory_zero_recenter
    hDensity hSob h0 hfree hret hefree heret hH psi hc
  have hL : Icc (a-c) 0 ⊆ U.domain := by
    intro t ht
    rw [hcenter.1]
    change c+t ∈ V.domain
    exact hAI ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hRight : Icc 0 (b-c) ⊆ U.domain := by
    intro t ht
    rw [hcenter.1]
    change c+t ∈ V.domain
    exact hBI ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnL : ‖U.path (sub_nonpos.mpr hac) hL‖ = ‖V.path hac hAI‖ := by
    have hLU : Icc (a-c) (c-c) ⊆ U.domain := by simpa only [sub_self] using hL
    simpa only [sub_self] using
      BilateralWindows.translated_path_norm V U c hcenter.2 hac hAI hLU
  have hnR : ‖U.path (sub_nonneg.mpr hcb) hRight‖ = ‖V.path hcb hBI‖ := by
    have hRU : Icc (c-c) (b-c) ⊆ U.domain := by simpa only [sub_self] using hRight
    simpa only [sub_self] using
      BilateralWindows.translated_path_norm V U c hcenter.2 hcb hBI hRU
  exact ⟨a-c, b-c, sub_nonpos.mpr hac, sub_nonneg.mpr hcb, hL, hRight,
    hlargeL.trans_eq hnL.symm, hlargeR.trans_eq hnR.symm⟩

/-- Spatial Palais--Smale for every supplied sequence of native times on the same
canonical orbit. The input states are exactly `V.state (t n)`. The proof supplies
BadDatum and bilateral graph windows before invoking the existing PS body. -/
theorem native_sequence_spatial_concentration
    (hDensity : OrdinaryH1Density) (hRel : OrdinaryRellichBall)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hExtract : OrdinaryLinearProfileExtraction hDensity hSob)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (cutoff : Highpass.Cutoff)
    (psi : EnergyState)
    (hEcW : criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd <
      totalEnergy alpha (normalizedBubbleState alpha))
    (hfuture : ¬ ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi))
    (hpast : ¬ ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi))
    (hNative : ∀ c ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi).domain,
      totalEnergy alpha
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi).state c) =
        criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
      gradientSquared
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi).state c) ≤
        kappa alpha * criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
      kappa alpha * criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd <
        gradientSquared (normalizedBubbleState alpha))
    (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi).domain) :
    ∃ (k : ℕ → ℕ) (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n)
      (y : ℕ → Space) (v : EnergyState),
      StrictMono k ∧
      Tendsto (fun n => (criticalAffineState (lambda n) (hlambda n) (y n)).symm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi).state
          (t (k n)))) atTop (𝓝 v) ∧
      totalEnergy alpha v = criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd := by
  classical
  let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
  let u : ℕ → EnergyState := fun n => V.state (t n)
  have henergy (n : ℕ) : totalEnergy alpha (u n) = Ec := (hNative (t n) (ht n)).1
  have hstable (n : ℕ) : StableDatum alpha (u n) := by
    have h := hNative (t n) (ht n)
    exact ⟨h.1.trans_lt hEcW,
      (pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr (h.2.1.trans_lt h.2.2)⟩
  have hubad (n : ℕ) : BadDatum hDensity hSob h0 hfree hret hefree heret hOrd (u n) := by
    refine ⟨hstable n, ?_⟩
    intro hfinite
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (u n)
    have hcenter := BilateralPathTools.actualMaximalTrajectory_zero_recenter
      hDensity hSob h0 hfree hret hefree heret hOrd psi (ht n)
    have hgradient : ∀ tau ∈ U.domain,
        pureGradientNorm (U.state tau) ≤ Real.sqrt (kappa alpha * Ec) := by
      intro tau htau
      have hshift : t n + tau ∈ V.domain := by
        have hmem := htau
        rw [hcenter.1] at hmem
        exact hmem
      rw [hcenter.2 htau]
      exact Real.sqrt_le_sqrt (hNative (t n + tau) hshift).2.1
    have hstate := MaximalFiniteSGlobal.state_cap_of_pure_gradient hSob U hgradient
    obtain ⟨R, hR, hcap⟩ := FiniteSActualX.uniform_compact_graph_of_finiteS
      hDensity hSob h0 hfree hret hOrd U hstate hfinite
    obtain ⟨_a, b, _ha, hb, _hL, hRight, _hlargeL, hlargeR⟩ :=
      prescribed_center_bilateral_windows hDensity hSob h0 hfree hret hefree heret hOrd
        psi hfuture hpast (t n) (ht n) R hR
    exact (not_lt_of_ge (hcap 0 b hb hRight)) hlargeR
  have hEu : Tendsto (fun n => totalEnergy alpha (u n)) atTop (𝓝 Ec) := by
    have heq : (fun n => totalEnergy alpha (u n)) = fun _ : ℕ => Ec := funext henergy
    rw [heq]
    exact tendsto_const_nhds
  have hw : BilateralGraphBounds.BilateralGraphWindows
      hDensity hSob h0 hfree hret hefree heret hOrd u := by
    intro n
    obtain ⟨a, b, ha, hb, hL, hRight, hlargeL, hlargeR⟩ :=
      prescribed_center_bilateral_windows hDensity hSob h0 hfree hret hefree heret hOrd
        psi hfuture hpast (t n) (ht n) ((n : ℝ)+1) (by positivity)
    exact ⟨a, b, ha, hb, hL, hRight, hlargeL.le, hlargeR.le⟩
  obtain ⟨k, lambda, hlambda, y, v, hk, hv, hEv, _hAv, _hstableV, _hfutureV, _hpastV⟩ :=
    ActualSpatialPalaisSmale.given_bilateral_bad_sequence_spatial_concentration
      hDensity hRel hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6
        hExtract hgen hUnique cutoff u hubad hEu hw
  exact ⟨k, lambda, hlambda, y, v, hk, hv, hEv⟩

end HartreeF.ActualNativeOrbitWindows
