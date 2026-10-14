import FLocalProductScale

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.LocalProfileProducts
open TimeHolder CompactCross CriticalAffine AffineMixed

/-- The literal overlap norm in two independent paper frames. -/
def frameProductNorm (q w v : ℝ) (f g : ℝ → Space → ℂ)
    (a b : ℝ) (y z : Space) (s r : ℝ) : ℝ≥0∞ :=
  mixedNorm volume volume 5 (ENNReal.ofReal q)
    (fun t x => ‖seedFrame a y s w f t x‖ * ‖seedFrame b z r v g t x‖)

theorem frameProductNorm_swap (q w v : ℝ) (f g : ℝ → Space → ℂ)
    (a b : ℝ) (y z : Space) (s r : ℝ) :
    frameProductNorm q w v f g a b y z s r = frameProductNorm q v w g f b a z y r s := by
  unfold frameProductNorm
  congr 1
  funext t x
  exact mul_comm _ _

/-- Critical local products have a positive scale-ratio gain, uniformly in both centers. -/
theorem box_frameProductNorm_scale {q w v A B : ℝ} (hq : 0 < q)
    (hw : (1/2:ℝ) ≤ w) (hv : (1/2:ℝ) ≤ v)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hcrit : 3/q+2/5=w+v)
    {S : Set Space} {I : Set ℝ} (hS : MeasurableSet S) (hI : MeasurableSet I)
    (hSf : volume S ≠ ∞) (hIf : volume I ≠ ∞)
    {f g : ℝ → Space → ℂ}
    (hf : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (hg : Continuous (fun z : ℝ × Space => g z.1 z.2))
    (hfB : ∀ t x, ‖f t x‖ ≤ A) (hgB : ∀ t x, ‖g t x‖ ≤ B)
    (hfS : ∀ t x, x ∉ S → f t x = 0) (hgS : ∀ t x, x ∉ S → g t x = 0)
    (hfI : ∀ t, t ∉ I → ∀ x, f t x = 0) (hgI : ∀ t, t ∉ I → ∀ x, g t x = 0) :
    ∃ C : ℝ≥0, ∀ a b : ℝ, 0 < a → 0 < b → ∀ y z : Space, ∀ s r : ℝ,
      frameProductNorm q w v f g a b y z s r ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ((min (a/b) (b/a))^(1/2 : ℝ)) := by
  let D : ℝ≥0∞ := ENNReal.ofReal (A*B) * volume S ^ (1/q) * volume I ^ (1/5 : ℝ)
  have hD : D ≠ ∞ := cylinder_budget_ne_top hq hSf hIf (A*B)
  refine ⟨D.toNNReal,fun a b ha hb y z s r => ?_⟩
  rw [ENNReal.coe_toNNReal hD]
  rcases le_total a b with hab | hba
  · have hh := parabolic_product_bound hq hA hB hcrit hS hI hSf hIf
      hf hg hfB hgB hfS hfI (inv_pos.mpr ha) (inv_pos.mpr hb)
      (-(a⁻¹ • y)) (-(b⁻¹ • z)) s r
    have hquot : b⁻¹/a⁻¹=a/b := by simp [div_eq_mul_inv,mul_comm]
    change frameProductNorm q w v f g a b y z s r ≤ _ at hh
    rw [hquot] at hh
    have hm : a/b ≤ b/a := by apply (div_le_div_iff₀ hb ha).mpr; nlinarith
    rw [min_eq_left hm]
    refine hh.trans ?_
    rw [mul_comm D]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge (div_pos ha hb) ((div_le_one hb).mpr hab) hv)) le_rfl
  · have hh := parabolic_product_bound hq hB hA (by linarith : 3/q+2/5=v+w)
      hS hI hSf hIf hg hf hgB hfB hgS hgI (inv_pos.mpr hb) (inv_pos.mpr ha)
      (-(b⁻¹ • z)) (-(a⁻¹ • y)) r s
    have hquot : a⁻¹/b⁻¹=b/a := by simp [div_eq_mul_inv,mul_comm]
    change frameProductNorm q v w g f b a z y r s ≤ _ at hh
    rw [hquot,mul_comm B A] at hh
    rw [frameProductNorm_swap q w v f g a b y z s r]
    have hm : b/a ≤ a/b := by apply (div_le_div_iff₀ ha hb).mpr; nlinarith
    rw [min_eq_right hm]
    refine hh.trans ?_
    rw [mul_comm D]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge (div_pos hb ha) ((div_le_one ha).mpr hba) hw)) le_rfl

#print axioms frameProductNorm
#print axioms frameProductNorm_swap
#print axioms box_frameProductNorm_scale
end HartreeF.LocalProfileProducts
