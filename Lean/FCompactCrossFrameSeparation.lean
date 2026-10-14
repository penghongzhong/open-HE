import FCompactCrossFrameScale
import FCompactCrossDoubleSeparation
import FCompactCrossNormalizedGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain

theorem cylinder_frameCrossNorm_space {α c R T : ℝ} (hHLS : OrdinaryHLS α c)
    (hR : 0 ≤ R)
    {U H V K : ℝ} (hU : 0 ≤ U) (hH : 0 ≤ H) (hV : 0 ≤ V) (hK : 0 ≤ K)
    {u h v k : ℝ → Space → ℂ}
    (hu : Continuous (fun q : ℝ × Space => u q.1 q.2))
    (hh : Continuous (fun q : ℝ × Space => h q.1 q.2))
    (hv : Continuous (fun q : ℝ × Space => v q.1 q.2))
    (hk : Continuous (fun q : ℝ × Space => k q.1 q.2))
    (huB : ∀ t x, ‖u t x‖ ≤ U) (hhB : ∀ t x, ‖h t x‖ ≤ H)
    (hvB : ∀ t x, ‖v t x‖ ≤ V) (hkB : ∀ t x, ‖k t x‖ ≤ K)
    (huS : ∀ t x, x ∉ Metric.closedBall 0 R → u t x = 0)
    (hvS : ∀ t x, x ∉ Metric.closedBall 0 R → v t x = 0)
    (huI : ∀ t, t ∉ Icc (-T) T → ∀ x, u t x = 0)
    (hvI : ∀ t, t ∉ Icc (-T) T → ∀ x, v t x = 0) :
    ∃ C : ℝ≥0, ∀ a b : ℝ, 0 < a → 0 < b → ∀ y z : Space, ∀ s r : ℝ,
      4*R^2*(a/b+b/a+2) < ‖y-z‖^2/(a*b) →
      frameCrossNorm α c u h v k a b y z s r ≤
        (C : ℝ≥0∞)*ENNReal.ofReal ((‖y-z‖^2/(a*b))^(-(3-α)/2)) := by
  let S : Set Space := Metric.closedBall 0 R
  let I : Set ℝ := Icc (-T) T
  have hS : MeasurableSet S := (isCompact_closedBall (0:Space) R).measurableSet
  have hI : MeasurableSet I := measurableSet_Icc
  have hSf : volume S ≠ ∞ := (isCompact_closedBall (0:Space) R).measure_lt_top.ne
  have hIf : volume I ≠ ∞ := isCompact_Icc.measure_lt_top.ne
  let B1 := separationBudget c ((3+α)*U^(2+α)*H) (V^(2+α)) S S I
  let B2 := separationBudget c (U^(3+α)) ((2+α)*V^(1+α)*K) S S I
  let D := ENNReal.ofReal ((2:ℝ)^(3-α))*max B1 B2
  have hD : D ≠ ∞ := by
    have hB1 : B1 ≠ ∞ := separationBudget_ne_top _ _ _ hSf hIf
    have hB2 : B2 ≠ ∞ := separationBudget_ne_top _ _ _ hSf hIf
    dsimp [D]; finiteness
  refine ⟨D.toNNReal,fun a b ha hb y z s r hsep => ?_⟩
  have hg := normalized_space_gap ha hb hR (norm_nonneg (y-z)) hsep
  have hdist := paper_space_support_separation ha hb y z hg.2
  have hp := pure_cross_double_offDiagonal hHLS (inv_pos.mpr ha) (inv_pos.mpr hb) hg.1
    (-(a⁻¹ • y)) (-(b⁻¹ • z)) s r hS hS hI hI hSf hSf hIf hIf
    hU hH hV hK hu hh hv hk huB hhB hvB hkB huS hvS huI hvI hdist
  have hi := hp.2.2.1
  have ho := hp.2.2.2
  rw [normalized_kernel_power ha hb (norm_nonneg _) α,
    ENNReal.ofReal_mul (by positivity : 0 ≤ (2:ℝ)^(3-α))] at hi ho
  rw [ENNReal.coe_toNNReal hD]
  have hh' := max_le (hi.trans (mul_le_mul' le_rfl (le_max_left B1 B2)))
    (ho.trans (mul_le_mul' le_rfl (le_max_right B1 B2)))
  simpa only [frameCrossNorm,seedFrame,D,mul_assoc,mul_comm,mul_left_comm] using hh'

theorem cylinder_frameCrossNorm_time {α c T : ℝ} (ha : 0 < α)
    (u h v k : ℝ → Space → ℂ)
    (huI : ∀ t, t ∉ Icc (-T) T → ∀ x, u t x = 0)
    (hvI : ∀ t, t ∉ Icc (-T) T → ∀ x, v t x = 0)
    {a b : ℝ} (haP : 0 < a) (hbP : 0 < b) (y z : Space) (s r : ℝ)
    (hgap : T*(a/b+b/a) < |a^2*s-b^2*r|/(a*b)) :
    frameCrossNorm α c u h v k a b y z s r = 0 := by
  have hdis := paper_time_support_disjoint haP hbP s r (normalized_time_gap haP hbP hgap)
  have hp := pure_cross_parabolic_time_disjoint ha c a⁻¹ b⁻¹
    (-(a⁻¹ • y)) (-(b⁻¹ • z)) s r u h v k hdis huI hvI
  simp only [frameCrossNorm,seedFrame,hp.1,hp.2,max_self]

#print axioms cylinder_frameCrossNorm_space
#print axioms cylinder_frameCrossNorm_time
end HartreeF.CompactCross
