import FLocalProductFrameScale
import FCompactCrossNormalizedGeometry
import FOrthogonalityScaleCutoff

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalProfileProducts
open TimeHolder CompactCross CriticalAffine AffineMixed

/-- Spatial separation makes the local product exactly zero, with the original
physical scales and centers and no nonlocal-potential estimate. -/
theorem cylinder_frameProductNorm_space {q w v R a b : ℝ} (hR : 0 ≤ R)
    {f g : ℝ → Space → ℂ}
    (hfS : ∀ t x, x ∉ Metric.closedBall 0 R → f t x = 0)
    (hgS : ∀ t x, x ∉ Metric.closedBall 0 R → g t x = 0)
    (ha : 0 < a) (hb : 0 < b) (y z : Space) (s r : ℝ)
    (hsep : R^2*(a/b+b/a+2) < ‖y-z‖^2/(a*b)) :
    frameProductNorm q w v f g a b y z s r = 0 := by
  have hzero : (fun t x => ‖seedFrame a y s w f t x‖ * ‖seedFrame b z r v g t x‖) = 0 := by
    funext t x
    by_cases hx : x ∈ (affine a⁻¹ (-(a⁻¹ • y))) ⁻¹' Metric.closedBall 0 R
    · have hx' : x ∉ (affine b⁻¹ (-(b⁻¹ • z))) ⁻¹' Metric.closedBall 0 R := by
        intro hz
        have hxy := paper_space_support_bound ha y x hx
        have hxz := paper_space_support_bound hb z x hz
        have htri : ‖y-z‖ ≤ ‖x-y‖+‖x-z‖ := by
          calc
            ‖y-z‖ = ‖(y-x)+(x-z)‖ := by congr 1; abel
            _ ≤ ‖y-x‖+‖x-z‖ := norm_add_le _ _
            _ = ‖x-y‖+‖x-z‖ := by rw [norm_sub_rev y x]
        have hh := (lt_div_iff₀ (mul_pos ha hb)).mp hsep
        rw [mul_assoc,physical_ratio_identity ha hb] at hh
        have hnon : 0 ≤ R*(a+b) := mul_nonneg hR (by positivity)
        have hbound : ‖y-z‖ ≤ R*(a+b) := by nlinarith
        have hsquare := (sq_le_sq₀ (norm_nonneg (y-z)) hnon).mpr hbound
        nlinarith
      rw [show seedFrame b z r v g t x = 0 from
        parabolicField_space_support b⁻¹ (-(b⁻¹ • z)) r v hgS t x hx',norm_zero,mul_zero]
      rfl
    · rw [show seedFrame a y s w f t x = 0 from
        parabolicField_space_support a⁻¹ (-(a⁻¹ • y)) s w hfS t x hx,norm_zero,zero_mul]
      rfl
  unfold frameProductNorm
  rw [hzero]
  simp [mixedNorm]

/-- The profile-clock convention gives the exact normalized temporal gap. -/
theorem cylinder_frameProductNorm_time {q w v T a b : ℝ}
    {f g : ℝ → Space → ℂ}
    (hfI : ∀ t, t ∉ Icc (-T) T → ∀ x, f t x = 0)
    (hgI : ∀ t, t ∉ Icc (-T) T → ∀ x, g t x = 0)
    (ha : 0 < a) (hb : 0 < b) (y z : Space) (s r : ℝ)
    (hgap : T*(a/b+b/a) < |a^2*s-b^2*r|/(a*b)) :
    frameProductNorm q w v f g a b y z s r = 0 := by
  have hd := paper_time_support_disjoint ha hb s r (normalized_time_gap ha hb hgap)
  have hzero : (fun t x => ‖seedFrame a y s w f t x‖ * ‖seedFrame b z r v g t x‖) = 0 := by
    funext t x
    by_cases ht : t ∈ (timeAffine a⁻¹ s) ⁻¹' Icc (-T) T
    · have ht' : t ∉ (timeAffine b⁻¹ r) ⁻¹' Icc (-T) T :=
        fun hh => Set.disjoint_left.mp hd ht hh
      rw [show seedFrame b z r v g t x = 0 from
        parabolicField_time_support b⁻¹ (-(b⁻¹ • z)) r v hgI t ht' x,norm_zero,mul_zero]
      rfl
    · rw [show seedFrame a y s w f t x = 0 from
        parabolicField_time_support a⁻¹ (-(a⁻¹ • y)) s w hfI t ht x,norm_zero,zero_mul]
      rfl
  unfold frameProductNorm
  rw [hzero]
  simp [mixedNorm]

/-- Whole-filter critical compact local-product decay from the original orthogonality
sum. All three norm estimates are derived from continuity and compact support. -/
theorem compact_frameProductNorm_orthogonality {ι : Type*} {l : Filter ι}
    {q w v : ℝ} (hq : 0 < q) (hw : (1/2:ℝ) ≤ w) (hv : (1/2:ℝ) ≤ v)
    (hcrit : 3/q+2/5=w+v) {f g : ℝ → Space → ℂ}
    (hf : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (hg : Continuous (fun z : ℝ × Space => g z.1 z.2))
    (hfC : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2))
    (hgC : HasCompactSupport (fun z : ℝ × Space => g z.1 z.2))
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => frameProductNorm q w v f g (a i) (b i) (y i) (z i) (s i) (r i)) l (𝓝 0) := by
  obtain ⟨A,hA,hfB⟩ := compact_seed_amplitude hf hfC
  obtain ⟨B,hB,hgB⟩ := compact_seed_amplitude hg hgC
  obtain ⟨R,T,hR,hT,hfS,hgS,hfI,hgI⟩ := compact_pair_cylinder hfC hgC
  have hSm : MeasurableSet (Metric.closedBall (0:Space) R) :=
    (isCompact_closedBall (0:Space) R).measurableSet
  have hSf : volume (Metric.closedBall (0:Space) R) ≠ ∞ :=
    (isCompact_closedBall (0:Space) R).measure_lt_top.ne
  have hIf : volume (Icc (-T) T) ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  obtain ⟨C,hC⟩ := box_frameProductNorm_scale hq hw hv hA hB hcrit hSm measurableSet_Icc
    hSf hIf hf hg hfB hgB hfS hgS hfI hgI
  apply OrthogonalityCutoff.tendsto_zero_of_scales_spatial_temporal ha hb C 0
    (δ := 1/2) (γ := 1) (K := R^2) (L := T)
    (by norm_num) (by norm_num) (by positivity) (by linarith) horth
  · exact fun i => hC (a i) (b i) (ha i) (hb i) (y i) (z i) (s i) (r i)
  · intro i hsep
    rw [cylinder_frameProductNorm_space (by linarith : 0 ≤ R) hfS hgS
      (ha i) (hb i) (y i) (z i) (s i) (r i) hsep]
    exact bot_le
  · intro i hgap
    exact cylinder_frameProductNorm_time hfI hgI (ha i) (hb i) (y i) (z i) (s i) (r i) hgap

#print axioms cylinder_frameProductNorm_space
#print axioms cylinder_frameProductNorm_time
#print axioms compact_frameProductNorm_orthogonality
end HartreeF.LocalProfileProducts
