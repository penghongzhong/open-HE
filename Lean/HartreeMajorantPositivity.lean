import HartreeGradientMajorantSum

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.GradientMajorants
open ForcingDomain

/-- Positivity of the literal Riesz integral, including its Lean total-integral convention. -/
theorem rieszConvolution_nonneg {α c : ℝ} (hc : 0 ≤ c) {f : Space → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : Space) : 0 ≤ rieszConvolution α c f x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _)) (hf y)

/-- The six-term function is pointwise nonnegative on the intended nonnegative inputs. -/
theorem majorantSum_nonneg {α c : ℝ} (hc : 0 ≤ c) {V W Y Z : Space → ℝ}
    (hV : ∀ x, 0 ≤ V x) (hW : ∀ x, 0 ≤ W x)
    (hY : ∀ x, 0 ≤ Y x) (hZ : ∀ x, 0 ≤ Z x) (x : Space) :
    0 ≤ majorantSum α c V W Y Z x := by
  have hp (a : ℝ) (y : Space) : 0 ≤ V y ^ a := Real.rpow_nonneg (hV y) a
  have h1 := rieszConvolution_nonneg (α := α) hc (fun y => hp (3+α) y) x
  have h2 := rieszConvolution_nonneg (α := α) hc (fun y => mul_nonneg (hp (2+α) y) (hW y)) x
  have h4 := rieszConvolution_nonneg (α := α) hc (fun y => mul_nonneg (hp (2+α) y) (hZ y)) x
  have h5 := rieszConvolution_nonneg (α := α) hc
    (fun y => mul_nonneg (mul_nonneg (hp (1+α) y) (hW y)) (hY y)) x
  have h6 := rieszConvolution_nonneg (α := α) hc (fun y => mul_nonneg (hp (2+α) y) (hY y)) x
  simp only [majorantSum, Pi.add_apply, majorant1, majorant2, majorant3, majorant4, majorant5, majorant6]
  exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg h1 (hp (1+α) x)) (hZ x))
    (mul_nonneg (mul_nonneg h2 (hp (1+α) x)) (hY x)))
    (mul_nonneg (mul_nonneg (mul_nonneg h1 (hp α x)) (hW x)) (hY x)))
    (mul_nonneg h4 (hp (2+α) x)))
    (mul_nonneg h5 (hp (2+α) x)))
    (mul_nonneg (mul_nonneg h6 (hp (1+α) x)) (hW x))

end HartreeF.GradientMajorants
