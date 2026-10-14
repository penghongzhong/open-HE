import HartreeDensitySplitDomain
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Native extension of the compact smooth weak test identity, under genuine
L1 domains, using explicit expanding cutoffs and dominated convergence. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace HartreeF.RieszWeakDerivative
open SobolevStretch CutoffApproximation WeakCutoffLp

theorem cutoff_derivative_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x v : Space), ‖fderiv ℝ (cutoff n) x v‖ ≤ C*‖v‖ := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (baseBump : Space → ℝ) := baseBump.contDiff
  obtain ⟨C,hC⟩ := (cutoff_gradient_hasCompactSupport baseBump.hasCompactSupport).exists_bound_of_continuous
    (cutoff_gradient_continuous hs)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C,hC0,?_⟩
  intro n x v
  rw [← inner_gradient_left]
  calc
    _ ≤ ‖gradient (cutoff n) x‖*‖v‖ := norm_inner_le_norm _ _
    _ ≤ C*‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [cutoff_gradient_formula,norm_smul,Real.norm_eq_abs,abs_of_pos (cutoffScale_pos n)]
      have hn : cutoffScale n ≤ 1 := by
        unfold cutoffScale
        apply (inv_le_one₀ (by positivity)).mpr
        linarith [Nat.cast_nonneg (α := ℝ) n]
      exact (mul_le_mul_of_nonneg_left (hC _) (cutoffScale_pos n).le).trans
        (mul_le_of_le_one_left hC0 hn)

theorem cutoff_derivative_eventually_zero (x v : Space) :
    ∀ᶠ n : ℕ in atTop, fderiv ℝ (cutoff n) x v = 0 := by
  obtain ⟨N,hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxn : ‖x‖ ≤ n := hN.le.trans (by exact_mod_cast hn)
  rw [← inner_gradient_left,cutoff_gradient_zero n hxn,inner_zero_left]

theorem integral_cutoff_mul_tendsto {f : Space → ℝ} (hf : Integrable f volume) :
    Tendsto (fun n => ∫ x, cutoff n x*f x) atTop (𝓝 (∫ x, f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => (cutoff_smooth n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable) hf.norm
  · intro n
    filter_upwards [] with x
    change ‖cutoff n x*f x‖ ≤ ‖f x‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (cutoff_nonneg n x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one n x)
  · filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoff_eventually_one x] with n hn
    change f x = cutoff n x*f x
    simp only [hn,one_mul]

theorem weak_gradient_noncompact_test {f : Space → ℝ} {G : Space → Space}
    (hw : HasWeakGradient f G) {ψ : Space → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : Space)
    (hprod : Integrable (fun x => f x*ψ x) volume)
    (hleft : Integrable (fun x => f x*fderiv ℝ ψ x v) volume)
    (hright : Integrable (fun x => ⟪G x,v⟫*ψ x) volume) :
    (∫ x, f x*fderiv ℝ ψ x v) = -(∫ x, ⟪G x,v⟫*ψ x) := by
  obtain ⟨C,hC0,hC⟩ := cutoff_derivative_uniform_bound
  have htest (n : ℕ) := (cutoff_smooth n).mul hψ
  have hformula (n : ℕ) (x : Space) :
      f x*fderiv ℝ (fun y => cutoff n y*ψ y) x v =
        cutoff n x*(f x*fderiv ℝ ψ x v)+(f x*ψ x)*fderiv ℝ (cutoff n) x v := by
    change f x*fderiv ℝ (cutoff n*ψ) x v = _
    rw [(((cutoff_smooth n).differentiable (by simp) x).hasFDerivAt.mul
      ((hψ.differentiable (by simp) x).hasFDerivAt)).fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  have hlimL : Tendsto (fun n => ∫ x, f x*fderiv ℝ (fun y => cutoff n y*ψ y) x v) atTop
      (𝓝 (∫ x, f x*fderiv ℝ ψ x v)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖f x*fderiv ℝ ψ x v‖+(C*‖v‖)*‖f x*ψ x‖)
      (fun n => hw.function_local.aestronglyMeasurable.mul
        (((htest n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable)
      (hleft.norm.add (hprod.norm.const_mul (C*‖v‖)))
    · intro n
      filter_upwards [] with x
      change ‖f x*fderiv ℝ (fun y => cutoff n y*ψ y) x v‖ ≤ _
      rw [hformula]
      calc
        _ ≤ ‖cutoff n x*(f x*fderiv ℝ ψ x v)‖+‖(f x*ψ x)*fderiv ℝ (cutoff n) x v‖ := norm_add_le _ _
        _ ≤ ‖f x*fderiv ℝ ψ x v‖+‖f x*ψ x‖*(C*‖v‖) := by
          simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (cutoff_nonneg n x)]
          exact add_le_add (mul_le_of_le_one_left (by positivity) (cutoff_le_one n x))
            (mul_le_mul_of_nonneg_left (hC n x v) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        _ = _ := by ring
    · filter_upwards [] with x
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_one x,cutoff_derivative_eventually_zero x v] with n hn hd
      change f x*fderiv ℝ ψ x v = f x*fderiv ℝ (fun y => cutoff n y*ψ y) x v
      rw [hformula,hn,hd]
      ring
  have hlimR := (integral_cutoff_mul_tendsto hright).neg
  apply tendsto_nhds_unique hlimL
  convert hlimR using 1
  funext n
  have ht := hw.integration_by_parts v (fun x => cutoff n x*ψ x) (htest n)
    ((cutoff_compact n).mul_right)
  rw [ht]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

#print axioms cutoff_derivative_uniform_bound
#print axioms cutoff_derivative_eventually_zero
#print axioms integral_cutoff_mul_tendsto
#print axioms weak_gradient_noncompact_test
end HartreeF.RieszWeakDerivative
