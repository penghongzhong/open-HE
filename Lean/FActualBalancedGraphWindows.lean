import FActualBilateralPathTools
import FL10TimePartition
import FMaximalFiniteSGlobalScattering

/-! Balanced windows from the actual temporal L10 mass.  No bilateral
badness or time-translation identity for S is assumed. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.BilateralWindows
open EnergySpace CriticalPathSpace CriticalPathRestriction IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open CriticalSourceBounds CriticalJointSources ActualSTail ActualPathPartitions
open AffinePath AffineMixed CriticalAffine MaximalTrajectory MaximalFiniteSGlobal
open BilateralPathTools TimePartition
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  affineCriticalPath LocalMildTrajectory.path

/-- A positive actual L10 mass admits a strictly interior half-mass point. -/
private theorem exists_L10_half_mass {E : Type*} [NormedAddCommGroup E]
    {a b T : ℝ} (hab : a≤b) {f : ℝ → E}
    (hf : MemLp f 10 (localMeasure a b)) (hT : 0<T)
    (hlarge : 2*T < lpNorm f 10 (localMeasure a b)) :
    ∃ c ∈ Ioo a b,
      T < lpNorm f 10 (localMeasure a c) ∧ T < lpNorm f 10 (localMeasure c b) := by
  let g : ℝ → ℝ := fun t => ‖f t‖^(10:ℕ)
  let mass : ℝ := ∫ t in a..b, g t
  have hg : IntervalIntegrable g volume a b := intervalIntegrable_norm_ten hab hf
  have hmass : mass = lpNorm f 10 (localMeasure a b)^(10:ℕ) :=
    integral_norm_ten_eq_lpNorm_pow hab hf
  have hpow : (2*T)^(10:ℕ) < mass := by
    rw [hmass]
    gcongr
  have hpowT : 0 < T^(10:ℕ) := pow_pos hT _
  have hhalf : T^(10:ℕ) < mass/2 := by
    rw [mul_pow] at hpow
    norm_num at hpow
    linarith
  have hmasspos : 0 < mass := by linarith
  have hcont : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  obtain ⟨c, hc, hleft⟩ := intermediate_value_Icc hab hcont
    (show mass/2 ∈ Icc (∫ t in a..a, g t) (∫ t in a..b, g t) by
      simp only [intervalIntegral.integral_same]
      change 0 ≤ mass/2 ∧ mass/2 ≤ mass
      constructor <;> linarith)
  have hac : a<c := by
    apply lt_of_le_of_ne hc.1
    intro heq
    have hz : (0:ℝ)=mass/2 := by simpa only [← heq, intervalIntegral.integral_same] using hleft
    linarith
  have hcb : c<b := by
    apply lt_of_le_of_ne hc.2
    intro heq
    have hz : mass=mass/2 := by simpa only [heq] using hleft
    linarith
  have hright : (∫ t in c..b, g t)=mass/2 := by
    have hsub := intervalIntegral.integral_interval_sub_left hg
      (intervalIntegrable_to_member hab hg hc)
    change mass - (∫ t in a..c, g t) = (∫ t in c..b, g t) at hsub
    rw [hleft] at hsub
    linarith
  have hfL : MemLp f 10 (localMeasure a c) :=
    hf.mono_measure (localMeasure_mono le_rfl hc.2)
  have hfR : MemLp f 10 (localMeasure c b) :=
    hf.mono_measure (localMeasure_mono hc.1 le_rfl)
  have hLpow : T^(10:ℕ) < lpNorm f 10 (localMeasure a c)^(10:ℕ) := by
    rw [← integral_norm_ten_eq_lpNorm_pow hac.le hfL]
    change T^(10:ℕ) < ∫ t in a..c, g t
    rw [hleft]
    exact hhalf
  have hRpow : T^(10:ℕ) < lpNorm f 10 (localMeasure c b)^(10:ℕ) := by
    rw [← integral_norm_ten_eq_lpNorm_pow hcb.le hfR]
    change T^(10:ℕ) < ∫ t in c..b, g t
    rw [hright]
    exact hhalf
  refine ⟨c, ⟨hac,hcb⟩, ?_, ?_⟩
  · by_contra h
    exact (not_le_of_gt hLpow) (pow_le_pow_left₀ lpNorm_nonneg (le_of_not_gt h) _)
  · by_contra h
    exact (not_le_of_gt hRpow) (pow_le_pow_left₀ lpNorm_nonneg (le_of_not_gt h) _)

/-- Split the genuine path-value realization, then identify its restrictions. -/
theorem exists_path_half_large_S (hDensity : OrdinaryH1Density) {K a b T : ℝ}
    (hSob : OrdinarySobolev K) (hab : a≤b) (q : CriticalPath (intervalMeasure a b))
    (hT : 0<T) (hlarge : ENNReal.ofReal (2*T) < pathValueSize (intervalMeasure a b) q) :
    ∃ (c : ℝ) (hac : a<c) (hcb : c<b),
      ENNReal.ofReal T < pathValueSize (intervalMeasure a c)
        (restrictPath le_rfl hac.le hcb.le q) ∧
      ENNReal.ofReal T < pathValueSize (intervalMeasure c b)
        (restrictPath hac.le hcb.le le_rfl q) := by
  let f := toLocalLp hab 10 (pathValueLp hDensity hSob q)
  have hf : MemLp (f : ℝ → ValueSpace) 10 (localMeasure a b) := Lp.memLp f
  have hsize : ENNReal.ofReal (lpNorm f 10 (localMeasure a b)) =
      pathValueSize (intervalMeasure a b) q := by
    rw [ofReal_lpNorm hf, ← Lp.enorm_def f, ← ofReal_norm]
    rw [show ‖f‖ = ‖pathValueLp hDensity hSob q‖ from toLocalLp_norm hab 10 _]
    rw [ofReal_norm, pathValueLp_enorm]
  have hreal : 2*T < lpNorm f 10 (localMeasure a b) := by
    by_contra h
    have he := ENNReal.ofReal_le_ofReal (le_of_not_gt h)
    exact (not_le_of_gt hlarge) (hsize.symm.trans_le he)
  obtain ⟨c, hc, hL, hR⟩ := exists_L10_half_mass hab hf hT hreal
  refine ⟨c, hc.1, hc.2, ?_, ?_⟩
  · rw [restricted_pathValueSize_eq hDensity hSob le_rfl hc.1.le hc.2.le,
      ← ofReal_lpNorm (hf.mono_measure (localMeasure_mono le_rfl hc.2.le))]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT.le |>.2 hL
  · rw [restricted_pathValueSize_eq hDensity hSob hc.1.le hc.2.le le_rfl,
      ← ofReal_lpNorm (hf.mono_measure (localMeasure_mono hc.1.le le_rfl))]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT.le |>.2 hR

/-- A record on the same original trajectory, retaining the true compact domain. -/
structure BalancedWindow {alpha kernel s : ℝ} {f : EnergyState}
    (M : LocalMildTrajectory alpha kernel s f) (R : ℝ) where
  left : ℝ
  center : ℝ
  right : ℝ
  left_lt_center : left<center
  center_lt_right : center<right
  within : Icc left right ⊆ M.domain
  left_graph : R < ‖M.path left_lt_center.le
    (fun _ ht => within ⟨ht.1, ht.2.trans center_lt_right.le⟩)‖
  right_graph : R < ‖M.path center_lt_right.le
    (fun _ ht => within ⟨left_lt_center.le.trans ht.1, ht.2⟩)‖

theorem BalancedWindow.center_mem {alpha kernel s R : ℝ} {f : EnergyState}
    {M : LocalMildTrajectory alpha kernel s f} (w : BalancedWindow M R) :
    w.center ∈ M.domain := w.within ⟨w.left_lt_center.le, w.center_lt_right.le⟩

/-- Total non-finite actual S produces two large true graph windows about
one interior center; it does not assert bilateral badness at a fixed center. -/
theorem exists_balanced_compact_windows (hDensity : OrdinaryH1Density)
    {K alpha kernel s R : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (M : LocalMildTrajectory alpha kernel s f) (hbad : ¬ FiniteSOnDomain M)
    (hR : 0<R) : Nonempty (BalancedWindow M R) := by
  classical
  let C := graphSConstant K
  have hC : 0≤C := graphSConstant_nonneg hSob
  let T := (C+1)*R
  have hT : 0<T := mul_pos (by linarith) hR
  have hex : ∃ (a b : ℝ) (hab : a≤b) (hI : Icc a b ⊆ M.domain),
      ENNReal.ofReal (2*T) < pathValueSize (intervalMeasure a b) (M.path hab hI) := by
    by_contra h
    apply hbad
    refine ⟨⟨2*T, by positivity⟩, ?_⟩
    intro a b hab hI
    have hle : pathValueSize (intervalMeasure a b) (M.path hab hI) ≤
        ENNReal.ofReal (2*T) := le_of_not_gt (fun hlt => h ⟨a,b,hab,hI,hlt⟩)
    simpa only [ENNReal.ofReal_eq_coe_nnreal (by positivity : 0≤2*T)] using hle
  obtain ⟨a,b,hab,hI,hlarge⟩ := hex
  obtain ⟨c,hac,hcb,hL,hRight⟩ := exists_path_half_large_S hDensity hSob hab
    (M.path hab hI) hT hlarge
  have graph_large {l r : ℝ} (q : CriticalPath (intervalMeasure l r))
      (hq : ENNReal.ofReal T < pathValueSize (intervalMeasure l r) q) : R < ‖q‖ := by
    by_contra hn
    have hbound : C*‖q‖ ≤ T := by
      have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hC
      dsimp [T]
      nlinarith
    exact (not_le_of_gt hq) ((pathValueSize_le_graph hDensity hSob q).trans
      (ENNReal.ofReal_le_ofReal hbound))
  have hIL : Icc a c ⊆ M.domain := fun _ ht => hI ⟨ht.1, ht.2.trans hcb.le⟩
  have hIR : Icc c b ⊆ M.domain := fun _ ht => hI ⟨hac.le.trans ht.1, ht.2⟩
  refine ⟨⟨a,c,b,hac,hcb,hI,?_,?_⟩⟩
  · rw [path_restrict M hab hI le_rfl hac.le hcb.le hIL]
    exact graph_large _ hL
  · rw [path_restrict M hab hI hac.le hcb.le le_rfl hIR]
    exact graph_large _ hRight

/-- Literal translated path identity and its graph norm consequence. -/
theorem translated_path_norm {alpha kernel s : ℝ} {f g : EnergyState}
    (M : LocalMildTrajectory alpha kernel s f) (U : LocalMildTrajectory alpha kernel 0 g)
    (c : ℝ) (heq : Set.EqOn U.state (fun t => M.state (c+t)) U.domain)
    {l r : ℝ} (hlr : l≤r) (hM : Icc l r ⊆ M.domain)
    (hU : Icc (l-c) (r-c) ⊆ U.domain) :
    ‖U.path (sub_le_sub_right hlr c) hU‖ = ‖M.path hlr hM‖ := by
  have hl : timeAffine 1 c (l-c)=l := by unfold timeAffine; ring
  have hr : timeAffine 1 c (r-c)=r := by unfold timeAffine; ring
  have hsource : Icc (timeAffine 1 c (l-c)) (timeAffine 1 c (r-c)) ⊆ M.domain := by
    simpa only [hl,hr] using hM
  have hstate : Set.EqOn U.state
      (fun t => affineState (by norm_num : (0:ℝ)<1) 0 (M.state (timeAffine 1 c t)))
      (Icc (l-c) (r-c)) := by
    intro t ht
    simpa only [affineState_one_zero, timeAffine, one_pow, one_mul, add_comm] using heq (hU ht)
  have hid := affine_path_of_state_eqOn M U (by norm_num : (0:ℝ)<1) 0 c (l-c) (r-c)
    (sub_le_sub_right hlr c) hsource hU hstate
  have hn := (congrArg norm hid).trans
    (affineCriticalPath_norm (by norm_num : (0:ℝ)<1) 0 c (l-c) (r-c)
      (sub_le_sub_right hlr c) _)
  simpa only [hl,hr] using hn

/-- The native zero-mark trajectory and both actual windows, including the
compact path identity needed for all later graph transports. -/
structure ZeroCenteredWindow {alpha kernel s : ℝ} {f : EnergyState}
    (M : LocalMildTrajectory alpha kernel s f)
    (Z : (g : EnergyState) → LocalMildTrajectory alpha kernel 0 g) (R : ℝ) where
  center : ℝ
  center_mem : center ∈ M.domain
  left : ℝ
  right : ℝ
  left_neg : left<0
  right_pos : 0<right
  domain_eq : (Z (M.state center)).domain = (fun t : ℝ => center+t) ⁻¹' M.domain
  state_eq : Set.EqOn (Z (M.state center)).state (fun t => M.state (center+t))
    (Z (M.state center)).domain
  left_within : Icc left 0 ⊆ (Z (M.state center)).domain
  right_within : Icc 0 right ⊆ (Z (M.state center)).domain
  left_graph : R < ‖(Z (M.state center)).path left_neg.le left_within‖
  right_graph : R < ‖(Z (M.state center)).path right_pos.le right_within‖
  path_identity : ∀ (A B : ℝ) (hAB : A≤B)
    (hM : Icc (timeAffine 1 center A) (timeAffine 1 center B) ⊆ M.domain)
    (hZ : Icc A B ⊆ (Z (M.state center)).domain),
    (Z (M.state center)).path hAB hZ =
      affineCriticalPath (by norm_num : (0:ℝ)<1) 0 center A B hAB
        (M.path (timeAffine_monotone (by norm_num : (0:ℝ)<1) center hAB) hM)

/-- Center one true large window and construct the same actual zero-mark U. -/
theorem actual_zero_centered_window (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s R : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (f : EnergyState)
    (hbad : ¬ FiniteSOnDomain
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f))
    (hR : 0<R) :
    Nonempty (ZeroCenteredWindow
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f)
      (fun g => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 g) R) := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  let Z := fun g => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 g
  obtain ⟨w⟩ := exists_balanced_compact_windows hDensity hSob M hbad hR
  let U := Z (M.state w.center)
  have hc : w.center ∈ M.domain := w.center_mem
  have hcenter := actualMaximalTrajectory_zero_recenter
    hDensity hSob h0 hfree hret hefree heret hH f hc
  have hL : Icc (w.left-w.center) 0 ⊆ U.domain := by
    intro t ht
    rw [hcenter.1]
    change w.center+t ∈ M.domain
    exact w.within ⟨by linarith [ht.1], by linarith [ht.2, w.center_lt_right]⟩
  have hR' : Icc 0 (w.right-w.center) ⊆ U.domain := by
    intro t ht
    rw [hcenter.1]
    change w.center+t ∈ M.domain
    exact w.within ⟨by linarith [ht.1, w.left_lt_center], by linarith [ht.2]⟩
  have hLM : Icc w.left w.center ⊆ M.domain :=
    fun _ ht => w.within ⟨ht.1, ht.2.trans w.center_lt_right.le⟩
  have hRM : Icc w.center w.right ⊆ M.domain :=
    fun _ ht => w.within ⟨w.left_lt_center.le.trans ht.1, ht.2⟩
  have hnL : ‖U.path (sub_nonpos.mpr w.left_lt_center.le) hL‖ =
      ‖M.path w.left_lt_center.le hLM‖ := by
    have hLU : Icc (w.left-w.center) (w.center-w.center) ⊆ U.domain := by
      simpa only [sub_self] using hL
    simpa only [sub_self] using translated_path_norm M U w.center hcenter.2
      w.left_lt_center.le hLM hLU
  have hnR : ‖U.path (sub_nonneg.mpr w.center_lt_right.le) hR'‖ =
      ‖M.path w.center_lt_right.le hRM‖ := by
    have hRU : Icc (w.center-w.center) (w.right-w.center) ⊆ U.domain := by
      simpa only [sub_self] using hR'
    simpa only [sub_self] using translated_path_norm M U w.center hcenter.2
      w.center_lt_right.le hRM hRU
  refine ⟨{ center := w.center, center_mem := hc,
    left := w.left-w.center, right := w.right-w.center,
    left_neg := sub_neg.mpr w.left_lt_center,
    right_pos := sub_pos.mpr w.center_lt_right,
    domain_eq := hcenter.1, state_eq := hcenter.2,
    left_within := hL, right_within := hR',
    left_graph := ?_, right_graph := ?_, path_identity := ?_ }⟩
  · exact hnL.symm ▸ w.left_graph
  · exact hnR.symm ▸ w.right_graph
  · intro A B hAB hM hZ
    apply affine_path_of_state_eqOn M U (by norm_num : (0:ℝ)<1) 0 w.center A B hAB hM hZ
    intro t ht
    simpa only [affineState_one_zero, timeAffine, one_pow, one_mul, add_comm] using hcenter.2 (hZ ht)

/-- A whole balanced sequence with data M(c_n), native zero-mark lifespans,
and graph windows strictly larger than n+1. -/
theorem actual_zero_centered_windows (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (f : EnergyState)
    (hbad : ¬ FiniteSOnDomain
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f)) :
    Nonempty ((n : ℕ) → ZeroCenteredWindow
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f)
      (fun g => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 g)
      ((n:ℝ)+1)) := by
  classical
  exact ⟨fun n => Classical.choice (actual_zero_centered_window
    hDensity hSob h0 hfree hret hefree heret hH f hbad (by positivity : (0:ℝ)<(n:ℝ)+1))⟩

end HartreeF.BilateralWindows
