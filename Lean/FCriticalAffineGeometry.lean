import WeakDirectionalStretch
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-! Actual isotropic affine pullback in three dimensions. The scale is positive;
all Jacobians, null-set transport and finite-Lp domains are proved. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.CriticalAffine

def affine (a : ℝ) (b : Space) (x : Space) : Space := a • x + b

def affineHomeomorph {a : ℝ} (ha : a ≠ 0) (b : Space) : Space ≃ₜ Space where
  toFun := affine a b
  invFun := fun x => a⁻¹ • (x-b)
  left_inv := by intro x; simp [affine, smul_smul, ha]
  right_inv := by intro x; simp [affine, smul_smul, ha]
  continuous_toFun := (continuous_id.const_smul a).add continuous_const
  continuous_invFun := (continuous_id.sub continuous_const).const_smul a⁻¹

theorem affine_quasiMeasurePreserving {a : ℝ} (ha : a ≠ 0) (b : Space) :
    Measure.QuasiMeasurePreserving (affine a b) volume volume :=
  (measurePreserving_add_right volume b).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume ha)

/-- The precise three-dimensional Lebesgue Jacobian. -/
theorem affine_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0 < a) (b : Space) (f : Space → F) :
    (∫ x, f (affine a b x)) = (a^3)⁻¹ • ∫ x, f x := by
  unfold affine
  rw [Measure.integral_comp_smul_of_nonneg volume (fun x => f (x+b)) a (hR := ha.le)]
  rw [integral_add_right_eq_self]
  simp

theorem affine_integrable {F : Type*} [NormedAddCommGroup F]
    {a : ℝ} (ha : a ≠ 0) (b : Space) {f : Space → F} (hf : Integrable f volume) :
    Integrable (fun x => f (affine a b x)) volume :=
  (hf.comp_add_right b).comp_smul ha

theorem affine_memLp {F : Type*} [NormedAddCommGroup F]
    {a : ℝ} (ha : a ≠ 0) (b : Space) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {f : Space → F} (hf : MemLp f p volume) :
    MemLp (fun x => f (affine a b x)) p volume := by
  have hm := hf.aestronglyMeasurable.comp_quasiMeasurePreserving
    (affine_quasiMeasurePreserving ha b)
  apply (integrable_norm_rpow_iff hm hp0 hpt).1
  exact affine_integrable ha b
    ((integrable_norm_rpow_iff hf.aestronglyMeasurable hp0 hpt).2 hf)

def valuePullback {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (b : Space) (f : Space → F) (x : Space) : F :=
  Real.sqrt a • f (affine a b x)

def gradientPullback {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (b : Space) (f : Space → F) (x : Space) : F :=
  (a * Real.sqrt a) • f (affine a b x)

theorem valuePullback_memLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0 < a) (b : Space) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {f : Space → F} (hf : MemLp f p volume) : MemLp (valuePullback a b f) p volume :=
  (affine_memLp ha.ne' b hp0 hpt hf).const_smul _

theorem gradientPullback_memLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0 < a) (b : Space) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    {f : Space → F} (hf : MemLp f p volume) : MemLp (gradientPullback a b f) p volume :=
  (affine_memLp ha.ne' b hp0 hpt hf).const_smul _

theorem valuePullback_sixth_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0 < a) (b : Space) (f : Space → F) :
    (∫ x, ‖valuePullback a b f x‖^6) = ∫ x, ‖f x‖^6 := by
  have hpow : (Real.sqrt a)^6 = a^3 := by
    rw [show (6:ℕ)=2*3 by norm_num, pow_mul, Real.sq_sqrt ha.le]
  simp only [valuePullback, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg a), mul_pow, hpow, integral_const_mul]
  rw [affine_integral ha b (fun x => ‖f x‖^6), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]

theorem gradientPullback_square_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0 < a) (b : Space) (f : Space → F) :
    (∫ x, ‖gradientPullback a b f x‖^2) = ∫ x, ‖f x‖^2 := by
  have hpow : (a * Real.sqrt a)^2 = a^3 := by
    rw [mul_pow, Real.sq_sqrt ha.le]; ring
  simp only [gradientPullback, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg ha.le (Real.sqrt_nonneg a)), mul_pow, hpow, integral_const_mul]
  rw [affine_integral ha b (fun x => ‖f x‖^2), smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]

#print axioms affineHomeomorph
#print axioms affine_quasiMeasurePreserving
#print axioms affine_integral
#print axioms affine_memLp
#print axioms valuePullback_sixth_integral
#print axioms gradientPullback_square_integral
end HartreeF.CriticalAffine
