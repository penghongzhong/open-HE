import FLocalProductSupport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.LocalProfileProducts
open TimeHolder CompactCross CriticalAffine AffineMixed

theorem product_budget_scale {a b q w v A B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : 0 < q) (hA : 0 ≤ A) (_hB : 0 ≤ B) (hcrit : 3/q+2/5=w+v)
    (y : Space) (s : ℝ) {S : Set Space} {I : Set ℝ}
    (hS : MeasurableSet S) (hI : MeasurableSet I) :
    ENNReal.ofReal ((a^w*A)*(b^v*B)) *
      volume ((affine a y) ⁻¹' S) ^ (1/q) *
      volume ((timeAffine a s) ⁻¹' I) ^ (1/5 : ℝ) =
    ENNReal.ofReal ((b/a)^v) *
      (ENNReal.ofReal (A*B) * volume S ^ (1/q) * volume I ^ (1/5 : ℝ)) := by
  rw [affine_preimage_volume ha y hS,timeAffine_preimage_volume ha s hI,
    ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg ha.le _) hA),
    ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),
    ENNReal.ofReal_mul (Real.rpow_nonneg hb.le _),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hq.le),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/5),
    jacobian_rpow ha 3,jacobian_rpow ha 2,ENNReal.ofReal_mul hA]
  calc
    _ = (ENNReal.ofReal (a^w) * ENNReal.ofReal (a^(-(3:ℝ)*(1/q))) *
        ENNReal.ofReal (a^(-(2:ℝ)*(1/5)))) * ENNReal.ofReal (b^v) *
      (ENNReal.ofReal A * ENNReal.ofReal B * volume S ^ (1/q) * volume I ^ (1/5 : ℝ)) := by ring
    _ = _ := by
      rw [ofReal_rpow_triple ha]
      have he : w+ -(3:ℝ)*(1/q)+ -(2:ℝ)*(1/5) = -v := by
        calc
          _ = w-(3/q+2/5) := by ring
          _ = -v := by rw [hcrit]; ring
      rw [he,← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
      congr 2
      rw [Real.div_rpow hb.le ha.le,Real.rpow_neg ha.le]
      ring

/-- One factor supplies both supports; the other only supplies its global amplitude.
The genuine mixed norm gains the other factor's critical scaling weight. -/
theorem parabolic_product_bound {q w v A B : ℝ} (hq : 0 < q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hcrit : 3/q+2/5=w+v)
    {S : Set Space} {I : Set ℝ} (hS : MeasurableSet S) (hI : MeasurableSet I)
    (hSf : volume S ≠ ∞) (hIf : volume I ≠ ∞)
    {f g : ℝ → Space → ℂ}
    (hf : Continuous (fun z : ℝ × Space => f z.1 z.2))
    (hg : Continuous (fun z : ℝ × Space => g z.1 z.2))
    (hfB : ∀ t x, ‖f t x‖ ≤ A) (hgB : ∀ t x, ‖g t x‖ ≤ B)
    (hfS : ∀ t x, x ∉ S → f t x = 0)
    (hfI : ∀ t, t ∉ I → ∀ x, f t x = 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y z : Space) (s r : ℝ) :
    mixedNorm volume volume 5 (ENNReal.ofReal q)
      (fun t x => ‖parabolicField a y s w f t x‖ * ‖parabolicField b z r v g t x‖) ≤
    ENNReal.ofReal ((b/a)^v) *
      (ENNReal.ofReal (A*B) * volume S ^ (1/q) * volume I ^ (1/5 : ℝ)) := by
  have hpreS : MeasurableSet ((affine a y) ⁻¹' S) := hS.preimage (by unfold affine; fun_prop)
  have hpreI : MeasurableSet ((timeAffine a s) ⁻¹' I) := hI.preimage (by unfold timeAffine; fun_prop)
  have hpreSf : volume ((affine a y) ⁻¹' S) ≠ ∞ := by
    rw [affine_preimage_volume ha y hS]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf
  have hpreIf : volume ((timeAffine a s) ⁻¹' I) ≠ ∞ := by
    rw [timeAffine_preimage_volume ha s hI]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIf
  have h := cylinder_mixed_bound
    (F := fun t x => ‖parabolicField a y s w f t x‖ * ‖parabolicField b z r v g t x‖)
    (M := (a^w*A)*(b^v*B)) hq
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg ha.le _) hA)
      (mul_nonneg (Real.rpow_nonneg hb.le _) hB))
    hpreS hpreI hpreSf hpreIf
    ((parabolicField_continuous y s w hf).norm.mul (parabolicField_continuous z r v hg).norm)
    (fun t x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul (parabolicField_amplitude ha y s w hfB t x)
        (parabolicField_amplitude hb z r v hgB t x) (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg ha.le _) hA))
    (fun t x hx => by rw [parabolicField_space_support a y s w hfS t x hx,norm_zero,zero_mul])
    (fun t ht x => by rw [parabolicField_time_support a y s w hfI t ht x,norm_zero,zero_mul])
  rwa [product_budget_scale ha hb hq hA hB hcrit y s hS hI] at h

#print axioms product_budget_scale
#print axioms parabolic_product_bound
end HartreeF.LocalProfileProducts
