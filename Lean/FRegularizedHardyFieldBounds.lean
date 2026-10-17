import FRegularizedHardyField
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
Author candidate imported from preserved uncompiled proof text.
Exact per-attempt native receipts determine status. All analytic domain,
integrability, derivative and IBP claims are proved in the source below.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace
namespace HartreeF.RegularizedHardy
open EnergySpace

lemma denominator_ge (ε : ℝ) (y x : V) : ε ≤ denominator ε y x := by
  dsimp [denominator]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma denominator_continuous (ε : ℝ) (y : V) : Continuous (denominator ε y) :=
  (show Differentiable ℝ (denominator ε y) from
    fun x => (denominator_hasFDerivAt ε y x).differentiableAt).continuous

lemma inverse_continuous {ε : ℝ} (hε : 0 < ε) (y : V) :
    Continuous (fun x => (denominator ε y x)⁻¹) :=
  (denominator_continuous ε y).inv₀ (fun x => (denominator_pos hε y x).ne')

lemma inverse_le {ε : ℝ} (hε : 0 < ε) (y x : V) :
    (denominator ε y x)⁻¹ ≤ ε⁻¹ := by
  simpa only [one_div] using
    one_div_le_one_div_of_le hε (denominator_ge ε y x)

lemma component_eq_coordinate (ε : ℝ) (y x : V) (j : Fin 3) :
    component ε y j x = field ε y x j := by
  simp [component, coordinate, EuclideanSpace.inner_single_left]

lemma component_sq_sum (ε : ℝ) (y x : V) :
    (∑ j : Fin 3, component ε y j x ^ 2) = ‖field ε y x‖ ^ 2 := by
  simp_rw [component_eq_coordinate]
  exact (EuclideanSpace.real_norm_sq_eq _).symm

lemma coordinate_sq_le (z : V) (j : Fin 3) : (z j)^2 ≤ ‖z‖^2 := by
  have h : |z j| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z j
  nlinarith [sq_abs (z j), abs_nonneg (z j), norm_nonneg z]

lemma component_continuous {ε : ℝ} (hε : 0 < ε) (y : V) (j : Fin 3) :
    Continuous (component ε y j) :=
  (show Differentiable ℝ (component ε y j) from
    fun x => (component_hasFDerivAt hε y x j).differentiableAt).continuous

/-- A uniform bound for every actual component, obtained from the vector norm. -/
lemma component_norm_le {ε : ℝ} (hε : 0 < ε) (y x : V) (j : Fin 3) :
    ‖component ε y j x‖ ≤ 1 / Real.sqrt ε := by
  calc
    ‖component ε y j x‖ = ‖field ε y x j‖ := by rw [component_eq_coordinate]
    _ ≤ ‖field ε y x‖ := PiLp.norm_apply_le _ _
    _ ≤ 1 / Real.sqrt (denominator ε y x) := field_norm_le_inverse_sqrt hε y x
    _ ≤ 1 / Real.sqrt ε := one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr hε) (Real.sqrt_le_sqrt (denominator_ge ε y x))

/-- Continuity of the literal diagonal derivative, proved from its computed formula. -/
lemma diagonal_continuous {ε : ℝ} (hε : 0 < ε) (y : V) (j : Fin 3) :
    Continuous (fun x => fderiv ℝ (component ε y j) x (coordinate j)) := by
  simp_rw [component_fderiv_coordinate hε]
  exact (inverse_continuous hε y).sub
    ((continuous_const.mul (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℝ) j).comp
      (continuous_id.sub continuous_const)).pow 2)).div
      ((denominator_continuous ε y).pow 2)
      (fun x => pow_ne_zero _ (denominator_pos hε y x).ne'))

/-- The native diagonal derivative has the uniform bound 3 / ε. -/
lemma diagonal_norm_le {ε : ℝ} (hε : 0 < ε) (y x : V) (j : Fin 3) :
    ‖fderiv ℝ (component ε y j) x (coordinate j)‖ ≤ 3 / ε := by
  have hd := denominator_pos hε y x
  have hq : ((x - y) j)^2 ≤ denominator ε y x :=
    (coordinate_sq_le (x - y) j).trans (by dsimp [denominator]; linarith)
  have hterm : 0 ≤ 2 * ((x - y) j)^2 / (denominator ε y x)^2 := by positivity
  have hterm_le : 2 * ((x - y) j)^2 / (denominator ε y x)^2 ≤
      2 * (denominator ε y x)⁻¹ := by
    calc
      _ ≤ 2 * denominator ε y x / (denominator ε y x)^2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by field_simp [hd.ne']
  have hinv : 0 ≤ (denominator ε y x)⁻¹ := (inv_pos.mpr hd).le
  have hlocal : |(denominator ε y x)⁻¹ -
      2 * ((x - y) j)^2 / (denominator ε y x)^2| ≤
      3 * (denominator ε y x)⁻¹ := by
    apply abs_le.mpr
    constructor <;> linarith
  rw [component_fderiv_coordinate hε, Real.norm_eq_abs]
  calc
    _ ≤ 3 * (denominator ε y x)⁻¹ := hlocal
    _ ≤ 3 * ε⁻¹ := mul_le_mul_of_nonneg_left (inverse_le hε y x) (by norm_num)
    _ = 3 / ε := by rw [div_eq_mul_inv]

lemma field_continuous {ε : ℝ} (hε : 0 < ε) (y : V) : Continuous (field ε y) :=
  (show Differentiable ℝ (field ε y) from
    fun x => (field_hasFDerivAt hε y x).differentiableAt).continuous

lemma field_norm_sq_le {ε : ℝ} (hε : 0 < ε) (y x : V) :
    ‖field ε y x‖^2 ≤ ε⁻¹ :=
  (field_norm_sq_le_inverse hε y x).trans (inverse_le hε y x)

end HartreeF.RegularizedHardy
