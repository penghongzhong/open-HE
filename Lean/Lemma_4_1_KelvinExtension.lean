import Lemma_4_1_KelvinGradient
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Piecewise
import Mathlib.Topology.MetricSpace.ProperSpace

/-! The actual three-dimensional Kelvin extension. The value on the axis is
zero. Compact support makes the pullback identically zero in an open cylinder
about that axis; this removes the apparent singularity before gluing. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

abbrev Space := ℝ × Plane

def radiusSq (z : Space) : ℝ := s z.2.1 z.2.2

def innerExtension (R : ℝ) (f : Space → ℝ) (z : Space) : ℝ :=
  if radiusSq z = 0 then 0 else f (z.1, inversion R z.2)

def extension (R : ℝ) (f : Space → ℝ) (z : Space) : ℝ :=
  if radiusSq z < R^2 then innerExtension R f z else f z

theorem radiusSq_nonneg (z : Space) : 0 ≤ radiusSq z := by
  unfold radiusSq s; positivity

theorem radiusSq_contDiff : ContDiff ℝ ∞ radiusSq := by
  unfold radiusSq s; fun_prop

theorem radiusSq_eq_zero_iff (z : Space) : radiusSq z = 0 ↔ z.2 = 0 := by
  simp only [radiusSq,s,Prod.ext_iff,Prod.fst_zero,Prod.snd_zero]
  constructor
  · intro h; constructor <;> nlinarith [sq_nonneg z.2.1,sq_nonneg z.2.2]
  · rintro ⟨h1,h2⟩; simp [h1,h2]

/-- A concrete support bound extracted from compactness, not an extra
hypothesis on the paper's smooth compactly supported input. -/
theorem compact_support_bounds {f : Space → ℝ} (hf : HasCompactSupport f) :
    ∃ M : ℝ, 0 < M ∧ ∀ z, f z ≠ 0 → |z.1| ≤ M ∧ radiusSq z ≤ M := by
  have hc : Continuous (fun z : Space => |z.1| + radiusSq z) := by
    exact continuous_fst.abs.add radiusSq_contDiff.continuous
  obtain ⟨M,hM⟩ := (hf.image hc).bddAbove
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  have h := hM (mem_image_of_mem _ (subset_closure hz))
  have h' : |z.1| + radiusSq z ≤ max M 1 := h.trans (le_max_left _ _)
  constructor <;> linarith [radiusSq_nonneg z,abs_nonneg z.1]

/-- Quantitative removal of the inversion singularity, uniform in the
longitudinal coordinate. -/
theorem innerExtension_zero_near_axis {R M : ℝ} (_hR : 0 < R) (hM : 0 < M)
    {f : Space → ℝ} (hb : ∀ z, f z ≠ 0 → radiusSq z ≤ M)
    {z : Space} (hz : radiusSq z < R^4 / M) : innerExtension R f z = 0 := by
  unfold innerExtension
  split_ifs with hzero
  · rfl
  by_contra hne
  have hpos : 0 < radiusSq z := lt_of_le_of_ne (radiusSq_nonneg z) (Ne.symm hzero)
  have hbound := hb (z.1,inversion R z.2) hne
  change s (inversion R z.2).1 (inversion R z.2).2 ≤ M at hbound
  rw [inversion, image_norm_sq R z.2.1 z.2.2 hzero] at hbound
  change R^4 / radiusSq z ≤ M at hbound
  have ha := (div_le_iff₀ hpos).mp hbound
  have hb' := (lt_div_iff₀ hM).mp hz
  nlinarith

theorem innerExtension_contDiff {R : ℝ} (hR : 0 < R) {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (innerExtension R f) := by
  obtain ⟨M,hM,hbound⟩ := compact_support_bounds hc
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : radiusSq z = 0
  · have hδ : 0 < R^4 / M := div_pos (pow_pos hR _) hM
    have hn : ∀ᶠ q in 𝓝 z, radiusSq q < R^4 / M :=
      radiusSq_contDiff.continuous.continuousAt.eventually (gt_mem_nhds (by rwa [hz]))
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Space => (0 : ℝ)) z).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    exact innerExtension_zero_near_axis hR hM (fun q hq => (hbound q hq).2) hq
  · have hi : ContDiffAt ℝ ∞ (fun q : Space => (q.1,inversion R q.2)) z := by
      unfold inversion kx ky
      have hd : s z.2.1 z.2.2 ≠ 0 := hz
      apply ContDiffAt.prodMk (by fun_prop)
      apply ContDiffAt.prodMk
      · exact (by fun_prop : ContDiffAt ℝ ∞ (fun q : Space => R^2*q.2.1) z).div
          radiusSq_contDiff.contDiffAt hd
      · exact (by fun_prop : ContDiffAt ℝ ∞ (fun q : Space => R^2*q.2.2) z).div
          radiusSq_contDiff.contDiffAt hd
    apply (hf.contDiffAt.comp z hi).congr_of_eventuallyEq
    have hn : ∀ᶠ q in 𝓝 z, radiusSq q ≠ 0 :=
      radiusSq_contDiff.continuous.continuousAt.eventually (isOpen_compl_singleton.mem_nhds hz)
    filter_upwards [hn] with q hq
    simp [innerExtension,hq]

theorem extension_circle {R : ℝ} (hR : 0 < R) (f : Space → ℝ)
    {z : Space} (hz : radiusSq z = R^2) : innerExtension R f z = f z := by
  have hne : radiusSq z ≠ 0 := by rw [hz]; exact pow_ne_zero _ hR.ne'
  rw [innerExtension,ite_eq_right hne,inversion_on_circle hR hz]

theorem extension_exterior {R : ℝ} (f : Space → ℝ) {z : Space}
    (hz : R^2 ≤ radiusSq z) : extension R f z = f z := by
  simp [extension,not_lt.mpr hz]


theorem extension_continuous {R : ℝ} (hR : 0 < R) {f : Space → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : Continuous (extension R f) := by
  apply Continuous.if _ (innerExtension_contDiff hR hf hc).continuous hf.continuous
  intro z hz
  exact extension_circle hR f
    (frontier_lt_subset_eq radiusSq_contDiff.continuous continuous_const hz)

theorem extension_hasCompactSupport (R : ℝ) {f : Space → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (extension R f) := by
  obtain ⟨M,hM,hbound⟩ := compact_support_bounds hc
  let B : ℝ := M + R^2 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) B)
  intro z hz
  have hpair : |z.1| ≤ M ∧ radiusSq z ≤ M + R^2 := by
    change extension R f z ≠ 0 at hz
    unfold extension at hz
    split_ifs at hz with hin
    · unfold innerExtension at hz
      split_ifs at hz with hzero
      · exact (hz rfl).elim
      have hs := hbound (z.1,inversion R z.2) hz
      exact ⟨hs.1, by linarith⟩
    · have hs := hbound z hz
      exact ⟨hs.1,by nlinarith [sq_nonneg R]⟩
  have hBsq : M + R^2 < B^2 := by dsimp [B]; nlinarith [sq_nonneg (M+R^2),sq_nonneg R]
  have hx : |z.2.1| ≤ B := by
    have hs := hpair.2
    unfold radiusSq s at hs
    nlinarith [sq_nonneg z.2.2,sq_abs z.2.1,abs_nonneg z.2.1]
  have hy : |z.2.2| ≤ B := by
    have hs := hpair.2
    unfold radiusSq s at hs
    nlinarith [sq_nonneg z.2.1,sq_abs z.2.2,abs_nonneg z.2.2]
  have ht : |z.1| ≤ B := by dsimp [B]; nlinarith [hpair.1,sq_nonneg R]
  simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,
    max_le_iff] using And.intro ht (And.intro hx hy)


#print axioms radiusSq_nonneg
#print axioms radiusSq_contDiff
#print axioms radiusSq_eq_zero_iff
#print axioms compact_support_bounds
#print axioms innerExtension_zero_near_axis
#print axioms innerExtension_contDiff
#print axioms extension_circle
#print axioms extension_exterior
#print axioms extension_continuous
#print axioms extension_hasCompactSupport
end BWork.Kelvin
