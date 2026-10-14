import HartreePowerCalculus

noncomputable section
set_option autoImplicit false
namespace HartreeF.WeakHartreeChain

def projectedLocalFactor (q : ℝ) (L : ℂ →L[ℝ] ℝ) : ℂ → ℝ := L ∘ localFactor q

theorem localFactor_norm {q : ℝ} (hq : 0 < q) (z : ℂ) :
    ‖localFactor q z‖ = ‖z‖^(q+1) := by
  rw [localFactor,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact (Real.rpow_add_one' (norm_nonneg z) (by linarith : q+1 ≠ 0)).symm

theorem projectedLocalFactor_contDiff_one {q : ℝ} (hq : 1 < q) (L : ℂ →L[ℝ] ℝ) :
    ContDiff ℝ 1 (projectedLocalFactor q L) :=
  L.contDiff.comp (localFactor_contDiff_one hq)

theorem projectedLocalFactor_fderiv {q : ℝ} (hq : 1 < q) (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    fderiv ℝ (projectedLocalFactor q L) z = L.comp (localFactorDerivative q z) :=
  (L.hasFDerivAt.comp z (localFactor_hasFDerivAt hq z)).fderiv

theorem projectedLocalFactor_norm_bound {q : ℝ} (hq : 1 < q)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (z : ℂ) :
    ‖projectedLocalFactor q L z‖ ≤ 1*‖z‖^(q+1) := by
  calc
    _ ≤ ‖L‖*‖localFactor q z‖ := L.le_opNorm _
    _ ≤ 1*‖localFactor q z‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = _ := by rw [localFactor_norm (by linarith)]

theorem projectedLocalFactor_fderiv_bound {q : ℝ} (hq : 1 < q)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (z : ℂ) :
    ‖fderiv ℝ (projectedLocalFactor q L) z‖ ≤ (q+1)*‖z‖^q := by
  rw [projectedLocalFactor_fderiv hq]
  calc
    _ ≤ ‖L‖*‖localFactorDerivative q z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*‖localFactorDerivative q z‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using localFactorDerivative_bound hq z

theorem reCLM_norm_le_one : ‖Complex.reCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  change ‖z.re‖ ≤ 1*‖z‖
  simpa only [one_mul,Real.norm_eq_abs] using Complex.abs_re_le_norm z

theorem imCLM_norm_le_one : ‖Complex.imCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  change ‖z.im‖ ≤ 1*‖z‖
  simpa only [one_mul,Real.norm_eq_abs] using Complex.abs_im_le_norm z

#print axioms localFactor_norm
#print axioms projectedLocalFactor_contDiff_one
#print axioms projectedLocalFactor_fderiv
#print axioms projectedLocalFactor_norm_bound
#print axioms projectedLocalFactor_fderiv_bound
#print axioms reCLM_norm_le_one
#print axioms imCLM_norm_le_one
end HartreeF.WeakHartreeChain
