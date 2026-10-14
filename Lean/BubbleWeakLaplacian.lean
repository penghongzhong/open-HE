import ActualBubbleFields
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! The actual bubble Laplacian and its compact-test weak equation. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace HartreeF.Bubble

/-- The literal trace of the classical derivative in the standard orthonormal basis. -/
def divergence (V : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, ⟪EuclideanSpace.basisFun (Fin 3) ℝ i,
    fderiv ℝ V x (EuclideanSpace.basisFun (Fin 3) ℝ i)⟫

theorem fderiv_bubbleGradient_apply (x v : Space) :
    fderiv ℝ bubbleGradient x v =
      (3 * (1 + ‖x‖ ^ 2) ^ (-5 / 2 : ℝ) * ⟪x, v⟫) • x -
        (1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ) • v := by
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).rpow_const
    (p := (-3 / 2 : ℝ)) (Or.inl (one_add_norm_sq_pos x).ne')).neg.smul
      (hasFDerivAt_id x)
  have hd : HasFDerivAt bubbleGradient _ x := h
  rw [hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, neg_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
  norm_num
  module

theorem divergence_bubbleGradient (x : Space) :
    divergence bubbleGradient x = -3 * bubble x ^ 5 := by
  simp only [divergence, fderiv_bubbleGradient_apply, inner_sub_right,
    real_inner_smul_right]
  simp only [EuclideanSpace.basisFun_inner, EuclideanSpace.inner_basisFun_real]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, ite_true, mul_one,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : (∑ i : Fin 3, 3 * (1 + ‖x‖ ^ 2) ^ (-5 / 2 : ℝ) * x i * x i) =
      3 * (1 + ‖x‖ ^ 2) ^ (-5 / 2 : ℝ) * ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  have ha : (1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ) =
      (1 + ‖x‖ ^ 2) ^ (-5 / 2 : ℝ) * (1 + ‖x‖ ^ 2) := by
    conv_rhs => rhs; rw [← Real.rpow_one (1 + ‖x‖ ^ 2)]
    rw [← Real.rpow_add (one_add_norm_sq_pos x)]
    norm_num
  have hb : bubble x ^ 5 = (1 + ‖x‖ ^ 2) ^ (-5 / 2 : ℝ) := by
    rw [bubble, ← Real.rpow_mul_natCast (one_add_norm_sq_pos x).le]
    norm_num
  rw [ha, hb]
  ring

theorem fderiv_bubbleGradient_component (v x w : Space) :
    fderiv ℝ (fun y => ⟪v, bubbleGradient y⟫) x w =
      ⟪v, fderiv ℝ bubbleGradient x w⟫ := by
  have h := (innerSL ℝ v).hasFDerivAt.comp x
    ((contDiff_bubbleGradient.differentiable (by simp)) x).hasFDerivAt
  exact congrArg (fun L : Space →L[ℝ] ℝ => L w) h.fderiv

/-- All three actual product domains needed for native scalar integration by parts. -/
theorem bubbleGradient_component_test_domains (v : Space) {φ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => ⟪v, bubbleGradient x⟫ * φ x) ∧
    Integrable (fun x => ⟪v, bubbleGradient x⟫ * fderiv ℝ φ x v) ∧
    Integrable (fun x => ⟪v, fderiv ℝ bubbleGradient x v⟫ * φ x) := by
  have hv : Continuous (fun x => ⟪v, bubbleGradient x⟫) :=
    continuous_const.inner continuous_bubbleGradient
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg : Continuous (fun x => ⟪v, fderiv ℝ bubbleGradient x v⟫) :=
    continuous_const.inner
      ((contDiff_bubbleGradient.continuous_fderiv (by simp)).clm_apply continuous_const)
  exact ⟨(hv.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left,
    (hv.mul hdφ).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v).mul_left,
    (hdg.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left⟩

theorem bubbleGradient_component_weak (v : Space) {φ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ x, ⟪v, bubbleGradient x⟫ * fderiv ℝ φ x v) =
      -(∫ x, ⟪v, fderiv ℝ bubbleGradient x v⟫ * φ x) := by
  have ht := bubbleGradient_component_test_domains v hφ hc
  have hd : Differentiable ℝ (fun x => ⟪v, bubbleGradient x⟫) :=
    (innerSL ℝ v).differentiable.comp (contDiff_bubbleGradient.differentiable (by simp))
  have hfg' : Integrable (fun x =>
      fderiv ℝ (fun y => ⟪v, bubbleGradient y⟫) x v * φ x) := by
    simpa only [fderiv_bubbleGradient_component] using ht.2.2
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hfg' ht.2.1 ht.1
    (fun x _ => hd x) (fun x _ => hφ.differentiable (by simp) x)
  simpa only [fderiv_bubbleGradient_component] using h

theorem bubble_gradient_pairing_eq_sum (φ : Space → ℝ) (x : Space) :
    ⟪bubbleGradient x, gradient φ x⟫ =
      ∑ i : Fin 3, ⟪EuclideanSpace.basisFun (Fin 3) ℝ i, bubbleGradient x⟫ *
        fderiv ℝ φ x (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [← e.sum_inner_mul_inner (bubbleGradient x) (gradient φ x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (bubbleGradient x), inner_gradient_right]
  rfl

/-- Both full weak-equation integrands are genuinely integrable. -/
theorem bubble_weak_laplacian_test_integrable {φ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => ⟪bubbleGradient x, gradient φ x⟫) ∧
    Integrable (fun x => 3 * bubble x ^ 5 * φ x) := by
  constructor
  · simp_rw [bubble_gradient_pairing_eq_sum]
    exact integrable_finsetSum _ (fun i _ =>
      (bubbleGradient_component_test_domains (EuclideanSpace.basisFun (Fin 3) ℝ i) hφ hc).2.1)
  · exact ((continuous_const.mul (continuous_bubble.pow 5)).mul hφ.continuous).integrable_of_hasCompactSupport
      hc.mul_left

/-- The native weak identity for the actual globally smooth three-dimensional bubble. -/
theorem bubble_weak_laplacian (φ : Space → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ x, ⟪bubbleGradient x, gradient φ x⟫) = ∫ x, 3 * bubble x ^ 5 * φ x := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  simp_rw [bubble_gradient_pairing_eq_sum]
  rw [integral_finsetSum _ (fun i _ => (bubbleGradient_component_test_domains (e i) hφ hc).2.1)]
  simp_rw [bubbleGradient_component_weak _ hφ hc]
  rw [Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun i _ => (bubbleGradient_component_test_domains (e i) hφ hc).2.2)]
  simp_rw [← Finset.sum_mul]
  change -(∫ x, divergence bubbleGradient x * φ x) = _
  simp_rw [divergence_bubbleGradient]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

#print axioms divergence
#print axioms fderiv_bubbleGradient_apply
#print axioms divergence_bubbleGradient
#print axioms fderiv_bubbleGradient_component
#print axioms bubbleGradient_component_test_domains
#print axioms bubbleGradient_component_weak
#print axioms bubble_gradient_pairing_eq_sum
#print axioms bubble_weak_laplacian_test_integrable
#print axioms bubble_weak_laplacian
end HartreeF.Bubble
