import FCompactCrossRatio
import FCompactCrossFrameGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain

def frameCrossNorm (α c : ℝ) (u h v k : ℝ → Space → ℂ)
    (a b : ℝ) (y z : Space) (s r : ℝ) : ℝ≥0∞ :=
  max (forcingNorm (innerCross α c (seedFrame a y s (1/2) u)
    (seedFrame a y s (3/2) h) (seedFrame b z r (1/2) v)))
    (forcingNorm (outerCross α c (seedFrame a y s (1/2) u)
      (seedFrame b z r (1/2) v) (seedFrame b z r (3/2) k)))

theorem box_frameCrossNorm_scale {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {S T : Set Space} {I J : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hSf : volume S ≠ ∞) (hTf : volume T ≠ ∞) (hIf : volume I ≠ ∞) (hJf : volume J ≠ ∞)
    {U H V K : ℝ} (hU : 0 ≤ U) (hH : 0 ≤ H) (hV : 0 ≤ V) (hK : 0 ≤ K)
    {u h v k : ℝ → Space → ℂ}
    (hu : Continuous (fun q : ℝ × Space => u q.1 q.2))
    (hh : Continuous (fun q : ℝ × Space => h q.1 q.2))
    (hv : Continuous (fun q : ℝ × Space => v q.1 q.2))
    (hk : Continuous (fun q : ℝ × Space => k q.1 q.2))
    (huB : ∀ t x, ‖u t x‖ ≤ U) (hhB : ∀ t x, ‖h t x‖ ≤ H)
    (hvB : ∀ t x, ‖v t x‖ ≤ V) (hkB : ∀ t x, ‖k t x‖ ≤ K)
    (huS : ∀ t x, x ∉ S → u t x = 0) (hvT : ∀ t x, x ∉ T → v t x = 0)
    (huI : ∀ t, t ∉ I → ∀ x, u t x = 0) (hvJ : ∀ t, t ∉ J → ∀ x, v t x = 0) :
    ∃ C : ℝ≥0, ∀ a b : ℝ, 0 < a → 0 < b → ∀ y z : Space, ∀ s r : ℝ,
      frameCrossNorm α c u h v k a b y z s r ≤ (C : ℝ≥0∞)*
        ENNReal.ofReal ((min (a/b) (b/a))^((3-α)/4)) := by
  obtain ⟨C1,h1⟩ := box_pure_cross_ratio_decay hHLS hS hT hI hSf hTf hIf hU hH hV hK
    hu hh hv hk huB hhB hvB hkB huS hvT huI
  obtain ⟨C2,h2⟩ := box_pure_cross_ratio_decay hHLS hT hS hJ hTf hSf hJf hV hK hU hH
    hv hk hu hh hvB hkB huB hhB hvT huS hvJ
  refine ⟨max C1 C2,fun a b ha hb y z s r => ?_⟩
  have hquot : b⁻¹/a⁻¹=a/b := by simp [div_eq_mul_inv,mul_comm]
  have hquot' : a⁻¹/b⁻¹=b/a := by simp [div_eq_mul_inv,mul_comm]
  rcases le_total a b with hab | hba
  · have hh1 := h1 a⁻¹ b⁻¹ (inv_pos.mpr ha) (inv_pos.mpr hb) ((inv_le_inv₀ hb ha).mpr hab)
      (-(a⁻¹ • y)) (-(b⁻¹ • z)) s r
    have hm : a/b ≤ b/a := by apply (div_le_div_iff₀ hb ha).mpr; nlinarith
    rw [min_eq_left hm]
    apply (max_le hh1.1 hh1.2.1).trans
    rw [hquot]
    exact mul_le_mul' (by exact_mod_cast le_max_left C1 C2) le_rfl
  · have hh2 := h2 b⁻¹ a⁻¹ (inv_pos.mpr hb) (inv_pos.mpr ha) ((inv_le_inv₀ ha hb).mpr hba)
      (-(b⁻¹ • z)) (-(a⁻¹ • y)) r s
    have hm : b/a ≤ a/b := by apply (div_le_div_iff₀ ha hb).mpr; nlinarith
    rw [min_eq_right hm]
    apply (max_le hh2.2.2.1 hh2.2.2.2).trans
    rw [hquot']
    exact mul_le_mul' (by exact_mod_cast le_max_right C1 C2) le_rfl

#print axioms box_frameCrossNorm_scale
end HartreeF.CompactCross
