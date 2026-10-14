import NormalizedProjectionBounds

noncomputable section
set_option autoImplicit false
namespace HartreeF.WeakHartreeChain

def weightedProjection (q : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ := ‖z‖^q • unitProjection z

theorem weightedProjection_difference_bound_ordered {q : ℝ} (hq : 1 < q) (z w : ℂ)
    (hzw : ‖z‖ ≤ ‖w‖) :
    ‖weightedProjection q z-weightedProjection q w‖ ≤
      (q+4)*(‖z‖+‖w‖)^(q-1)*‖z-w‖ := by
  have he : weightedProjection q z-weightedProjection q w =
      ‖z‖^q • (unitProjection z-unitProjection w)+
        (‖z‖^q-‖w‖^q) • unitProjection w := by
    unfold weightedProjection
    module
  have hr : ‖z‖^q = ‖z‖^(q-1)*‖z‖ := by
    convert (Real.rpow_add_one' (norm_nonneg z) (by linarith : q-1+1 ≠ 0)) using 1
    congr 1
    ring
  have hfirst : ‖‖z‖^q • (unitProjection z-unitProjection w)‖ ≤
      4*(‖z‖+‖w‖)^(q-1)*‖z-w‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      _ ≤ ‖z‖^q*(2*‖NormedSpace.normalize z-NormedSpace.normalize w‖) :=
        mul_le_mul_of_nonneg_left (unitProjection_difference_bound z w) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = (2*‖z‖^(q-1))*(‖z‖*‖NormedSpace.normalize z-NormedSpace.normalize w‖) := by rw [hr]; ring
      _ ≤ (2*‖z‖^(q-1))*(2*‖z-w‖) :=
        mul_le_mul_of_nonneg_left (weighted_normalize_difference_le z w hzw) (by positivity)
      _ ≤ (2*(‖z‖+‖w‖)^(q-1))*(2*‖z-w‖) := by
        gcongr
        exact le_add_of_nonneg_right (norm_nonneg w)
      _ = _ := by ring
  have hsecond : ‖(‖z‖^q-‖w‖^q) • unitProjection w‖ ≤
      q*(‖z‖+‖w‖)^(q-1)*‖z-w‖ := by
    rw [norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (unitProjection_norm_le_one w)).trans
      (density_difference_bound hq z w)
  rw [he]
  have ht := norm_add_le (‖z‖^q • (unitProjection z-unitProjection w))
    ((‖z‖^q-‖w‖^q) • unitProjection w)
  nlinarith

theorem weightedProjection_difference_bound {q : ℝ} (hq : 1 < q) (z w : ℂ) :
    ‖weightedProjection q z-weightedProjection q w‖ ≤
      (q+4)*(‖z‖+‖w‖)^(q-1)*‖z-w‖ := by
  rcases le_total ‖z‖ ‖w‖ with hzw|hwz
  · exact weightedProjection_difference_bound_ordered hq z w hzw
  · simpa only [add_comm,norm_sub_rev] using weightedProjection_difference_bound_ordered hq w z hwz

#print axioms weightedProjection_difference_bound_ordered
#print axioms weightedProjection_difference_bound
end HartreeF.WeakHartreeChain
