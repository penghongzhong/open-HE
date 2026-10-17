import FEnergyBanach
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Author candidate based on an uncompiled source draft.
Exact per-attempt native receipts determine the status of this author source.
The source gives proof attempts, not assumptions for the desired Hardy estimate.
The explicit divergence is derived from the actual component Frechet derivatives.
`EnergySpace.V` is literally `EuclideanSpace ℝ (Fin 3)` and is definitionally the
same Euclidean domain as the F `SobolevStretch.Space` abbreviation.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace
namespace HartreeF.RegularizedHardy
open EnergySpace

/-- Positive regularization of the squared translated radius. -/
def denominator (ε : ℝ) (y x : V) : ℝ := ε + ‖x - y‖ ^ 2

/-- The actual regularized vector field, not a divergence certificate. -/
def field (ε : ℝ) (y x : V) : V := (denominator ε y x)⁻¹ • (x - y)

def component (ε : ℝ) (y : V) (j : Fin 3) (x : V) : ℝ :=
  innerSL ℝ (coordinate j) (field ε y x)

/-- Divergence is the sum of actual coordinate Frechet derivatives. -/
def divergence (ε : ℝ) (y x : V) : ℝ :=
  ∑ j : Fin 3, fderiv ℝ (component ε y j) x (coordinate j)

theorem denominator_pos {ε : ℝ} (hε : 0 < ε) (y x : V) :
    0 < denominator ε y x :=
  add_pos_of_pos_of_nonneg hε (sq_nonneg _)

theorem denominator_hasFDerivAt (ε : ℝ) (y x : V) :
    HasFDerivAt (denominator ε y) (2 • innerSL ℝ (x - y)) x := by
  have h := (((hasFDerivAt_id x).sub_const y).norm_sq).const_add ε
  change HasFDerivAt (fun z : V => ε + ‖z - y‖ ^ 2)
    (2 • innerSL ℝ (x - y)) x
  simpa only [id_eq, ContinuousLinearMap.comp_id] using h

/-- Kept in the precise form returned by the inverse-function chain rule. -/
def inverseDerivative (ε : ℝ) (y x : V) : V →L[ℝ] ℝ :=
  (-(denominator ε y x ^ 2)⁻¹) • (2 • innerSL ℝ (x - y))

theorem inverse_hasFDerivAt {ε : ℝ} (hε : 0 < ε) (y x : V) :
    HasFDerivAt (fun z => (denominator ε y z)⁻¹)
      (inverseDerivative ε y x) x := by
  simpa only [inverseDerivative, Function.comp_def] using
    (hasDerivAt_inv (denominator_pos hε y x).ne').comp_hasFDerivAt x
      (denominator_hasFDerivAt ε y x)

/-- Genuine derivative of the vector field, in native scalar-product-rule form. -/
def fieldDerivative (ε : ℝ) (y x : V) : V →L[ℝ] V :=
  (denominator ε y x)⁻¹ • ContinuousLinearMap.id ℝ V +
    (inverseDerivative ε y x).smulRight (x - y)

theorem field_hasFDerivAt {ε : ℝ} (hε : 0 < ε) (y x : V) :
    HasFDerivAt (field ε y) (fieldDerivative ε y x) x := by
  exact (inverse_hasFDerivAt hε y x).smul ((hasFDerivAt_id x).sub_const y)

theorem component_hasFDerivAt {ε : ℝ} (hε : 0 < ε)
    (y x : V) (j : Fin 3) :
    HasFDerivAt (component ε y j)
      ((innerSL ℝ (coordinate j)).comp (fieldDerivative ε y x)) x := by
  exact (innerSL ℝ (coordinate j)).hasFDerivAt.comp x (field_hasFDerivAt hε y x)

/-- The diagonal component is computed, rather than supplied as an IBP premise. -/
theorem component_fderiv_coordinate {ε : ℝ} (hε : 0 < ε)
    (y x : V) (j : Fin 3) :
    fderiv ℝ (component ε y j) x (coordinate j) =
      (denominator ε y x)⁻¹ -
        2 * ((x - y) j)^2 / (denominator ε y x)^2 := by
  rw [(component_hasFDerivAt hε y x j).fderiv]
  simp only [fieldDerivative, inverseDerivative, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, inner_add_right, real_inner_smul_right,
    smul_eq_mul]
  simp only [coordinate, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  simp only [PiLp.single_apply, ite_true]
  ring

/-- Exact three-dimensional divergence. -/
theorem divergence_eq {ε : ℝ} (hε : 0 < ε) (y x : V) :
    divergence ε y x = (3 * ε + ‖x - y‖^2) / (denominator ε y x)^2 := by
  unfold divergence
  simp_rw [component_fderiv_coordinate hε]
  have hn := EuclideanSpace.real_norm_sq_eq (x - y)
  simp only [Fin.sum_univ_three] at hn ⊢
  have hd := (denominator_pos hε y x).ne'
  field_simp [hd]
  dsimp [denominator] at *
  nlinarith

/-- The exact positive remainder is 2ε / D². -/
theorem divergence_sub_inverse {ε : ℝ} (hε : 0 < ε) (y x : V) :
    divergence ε y x - (denominator ε y x)⁻¹ =
      2 * ε / (denominator ε y x)^2 := by
  rw [divergence_eq hε]
  have hd := (denominator_pos hε y x).ne'
  field_simp [hd]
  dsimp [denominator]
  ring

theorem inverse_le_divergence {ε : ℝ} (hε : 0 < ε) (y x : V) :
    (denominator ε y x)⁻¹ ≤ divergence ε y x := by
  have h := divergence_sub_inverse hε y x
  have hp : 0 ≤ 2 * ε / (denominator ε y x)^2 := by positivity
  linarith

theorem field_norm {ε : ℝ} (hε : 0 < ε) (y x : V) :
    ‖field ε y x‖ = ‖x - y‖ / denominator ε y x := by
  rw [field, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (denominator_pos hε y x))]
  ring

/-- This square bound is enough for the sharp constant-4 Young/IBP proof. -/
theorem field_norm_sq_le_inverse {ε : ℝ} (hε : 0 < ε) (y x : V) :
    ‖field ε y x‖^2 ≤ (denominator ε y x)⁻¹ := by
  have hd := denominator_pos hε y x
  have hz : ‖x - y‖^2 ≤ denominator ε y x := by
    dsimp [denominator]
    linarith
  calc
    ‖field ε y x‖^2 = ‖x - y‖^2 / (denominator ε y x)^2 := by
      rw [field_norm hε, div_pow]
    _ ≤ denominator ε y x / (denominator ε y x)^2 :=
      div_le_div_of_nonneg_right hz (sq_nonneg _)
    _ = (denominator ε y x)⁻¹ := by field_simp [hd.ne']

theorem field_norm_le_inverse_sqrt {ε : ℝ} (hε : 0 < ε) (y x : V) :
    ‖field ε y x‖ ≤ 1 / Real.sqrt (denominator ε y x) := by
  have hd := denominator_pos hε y x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [one_div, inv_pow, Real.sq_sqrt hd.le] using
    field_norm_sq_le_inverse hε y x

/-- Pointwise Young inequality with both real and imaginary coordinates retained. -/
theorem complex_coordinate_young (a g : ℂ) (t : ℝ) :
    -(2 * t * (star a * g).re) ≤
      (1 / 2 : ℝ) * t^2 * ‖a‖^2 + 2 * ‖g‖^2 := by
  have hr := sq_nonneg (2 * g.re + t * a.re)
  have hi := sq_nonneg (2 * g.im + t * a.im)
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [hr, hi]

end HartreeF.RegularizedHardy
