import F121AffineWeakPairing
import Mathlib.Analysis.Normed.Group.Bounded

/-! All three escaping affine regimes on the actual coordinate L2 space. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Paper121WeakEscape
open EnergySpace CriticalAffine Paper121WeakPairing

theorem pairing_tendsto_zero_of_scale_zero
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    (hzero : Tendsto a atTop (𝓝 0)) (G H : L2) :
    Tendsto (fun n => inner ℝ (gradientAffineL2 (ha n) (b n) G) H) atTop (𝓝 0) := by
  apply weak_pairing_of_schwartz a ha b
  intro φ ψ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hc : Tendsto (fun n => a n * Real.sqrt (a n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      hzero.mul ((Real.continuous_sqrt.tendsto 0).comp hzero)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => schwartz_pairing_small_bound (ha n) (b n) φ ψ)
  simpa only [zero_mul] using hc.mul_const
    (SchwartzMap.seminorm ℝ 0 0 φ * ∫ x, ‖ψ x‖)

theorem pairing_tendsto_zero_of_scale_infty
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    (hinfty : Tendsto a atTop atTop) (G H : L2) :
    Tendsto (fun n => inner ℝ (gradientAffineL2 (ha n) (b n) G) H) atTop (𝓝 0) := by
  apply weak_pairing_of_schwartz a ha b
  intro φ ψ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hi : Tendsto (fun n => (a n)⁻¹) atTop (𝓝 0) := hinfty.inv_tendsto_atTop
  have hc : Tendsto (fun n => (a n)⁻¹ * Real.sqrt (a n)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using
      hi.mul ((Real.continuous_sqrt.tendsto 0).comp hi)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => schwartz_pairing_large_bound (ha n) (b n) φ ψ)
  simpa only [zero_mul] using hc.mul_const
    ((∫ x, ‖φ x‖) * SchwartzMap.seminorm ℝ 0 0 ψ)

theorem pairing_tendsto_zero_of_center_infty
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    {A : ℝ} (hbound : ∀ n, a n ≤ A)
    (hinfty : Tendsto (fun n => ‖b n‖) atTop atTop) (G H : L2) :
    Tendsto (fun n => inner ℝ (gradientAffineL2 (ha n) (b n) G) H) atTop (𝓝 0) := by
  apply weak_pairing_of_schwartz a ha b
  intro φ ψ
  simp_rw [schwartz_pairing]
  have hA : 0 < A := (ha 0).trans_le (hbound 0)
  let C : ℝ := A * Real.sqrt A
  have hC : 0 ≤ C := mul_nonneg hA.le (Real.sqrt_nonneg _)
  have hcoeff (n : ℕ) : a n * Real.sqrt (a n) ≤ C :=
    mul_le_mul (hbound n) (Real.sqrt_le_sqrt (hbound n))
      (Real.sqrt_nonneg _) hA.le
  have hpoint (x : Space) :
      Tendsto (fun n => gradientPullback (a n) (b n) φ x) atTop (𝓝 0) := by
    have hnorm : Tendsto (fun n => ‖affine (a n) (b n) x‖) atTop atTop := by
      apply tendsto_atTop.2
      intro R
      filter_upwards [hinfty.eventually_ge_atTop (R + A * ‖x‖)] with n hn
      have htri : ‖b n‖ ≤ ‖affine (a n) (b n) x‖ + a n * ‖x‖ := by
        calc
          ‖b n‖ = ‖(a n • x + b n) - a n • x‖ := by congr 1; abel
          _ ≤ ‖a n • x + b n‖ + ‖a n • x‖ := norm_sub_le _ _
          _ = _ := by simp only [norm_smul, Real.norm_of_nonneg (ha n).le, affine]
      have hm := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg x)
      linarith
    have hescape : Tendsto (fun n => affine (a n) (b n) x) atTop (cocompact Space) := by
      simpa only [Metric.cobounded_eq_cocompact] using
        (tendsto_norm_atTop_iff_cobounded.mp hnorm)
    have hφ := φ.tendsto_cocompact.comp hescape
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => show
      ‖gradientPullback (a n) (b n) φ x‖ ≤ C * ‖φ (affine (a n) (b n) x)‖ from by
        rw [gradientPullback, norm_smul, Real.norm_of_nonneg
          (mul_nonneg (ha n).le (Real.sqrt_nonneg _))]
        exact mul_le_mul_of_nonneg_right (hcoeff n) (norm_nonneg _))
    simpa only [Function.comp_def, norm_zero, mul_zero] using hφ.norm.const_mul C
  have hlim : Tendsto (fun n => ∫ x,
      inner ℝ (gradientPullback (a n) (b n) φ x) (ψ x)) atTop
        (𝓝 (∫ _x : Space, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun x => (C * SchwartzMap.seminorm ℝ 0 0 φ) * ‖ψ x‖)
    · exact Eventually.of_forall fun n =>
        (by unfold gradientPullback affine; fun_prop : Continuous
          (fun x => inner ℝ (gradientPullback (a n) (b n) φ x) (ψ x))).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun x => by
        calc
          ‖inner ℝ (gradientPullback (a n) (b n) φ x) (ψ x)‖ ≤
              ‖gradientPullback (a n) (b n) φ x‖ * ‖ψ x‖ := norm_inner_le_norm _ _
          _ = ((a n * Real.sqrt (a n)) * ‖φ (affine (a n) (b n) x)‖) * ‖ψ x‖ := by
            rw [gradientPullback, norm_smul, Real.norm_of_nonneg
              (mul_nonneg (ha n).le (Real.sqrt_nonneg _))]
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul (hcoeff n) (SchwartzMap.norm_le_seminorm ℝ φ _)
              (norm_nonneg _) hC) (norm_nonneg _)
    · exact ψ.integrable.norm.const_mul _
    · exact Eventually.of_forall fun x => by
        simpa only [inner_zero_left] using (hpoint x).inner
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => ψ x) atTop (𝓝 (ψ x)))
  simpa only [integral_zero] using hlim

end HartreeF.Paper121WeakEscape
