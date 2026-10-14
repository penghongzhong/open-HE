import Lemma_4_1_KelvinFrechet
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Concrete Kelvin change of variables on the punctured disk and exterior.
Mathlib's general Jacobian theorem is instantiated, not postulated. The
integrability equivalence is retained alongside the Bochner integral identity.
The global H1 gluing and the full angular inequality are still separate. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace BWork.Kelvin

local instance : (volume : Measure Plane).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

def innerDisk (R : ℝ) : Set Plane := {p | 0 < s p.1 p.2 ∧ s p.1 p.2 < R^2}
def exteriorDisk (R : ℝ) : Set Plane := {p | R^2 < s p.1 p.2}

theorem innerDisk_measurable (R : ℝ) : MeasurableSet (innerDisk R) := by
  have hc : Continuous (fun p : Plane => s p.1 p.2) := by unfold s; fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioo).measurableSet

theorem inversion_inner_mem {R : ℝ} (hR : 0 < R) {p : Plane} (hp : p ∈ innerDisk R) :
    inversion R p ∈ exteriorDisk R := by
  change R^2 < s (inversion R p).1 (inversion R p).2
  rw [show s (inversion R p).1 (inversion R p).2 = R^4/s p.1 p.2 from
    image_norm_sq R p.1 p.2 hp.1.ne']
  apply (lt_div_iff₀ hp.1).mpr
  nlinarith [mul_pos (sq_pos_of_pos hR) (sub_pos.mpr hp.2)]

theorem inversion_exterior_mem {R : ℝ} (hR : 0 < R) {p : Plane} (hp : p ∈ exteriorDisk R) :
    inversion R p ∈ innerDisk R := by
  have hp0 : 0 < s p.1 p.2 := (sq_pos_of_pos hR).trans hp
  change 0 < s (inversion R p).1 (inversion R p).2 ∧
    s (inversion R p).1 (inversion R p).2 < R^2
  rw [show s (inversion R p).1 (inversion R p).2 = R^4/s p.1 p.2 from
    image_norm_sq R p.1 p.2 hp0.ne']
  constructor
  · exact div_pos (pow_pos hR 4) hp0
  · apply (div_lt_iff₀ hp0).mpr
    nlinarith [mul_pos (sq_pos_of_pos hR) (sub_pos.mpr hp)]

theorem inversion_injOn_inner {R : ℝ} (hR : 0 < R) : InjOn (inversion R) (innerDisk R) := by
  intro p hp z hz he
  have hh := congrArg (inversion R) he
  rwa [inversion_involutive R p hR.ne' hp.1.ne',
    inversion_involutive R z hR.ne' hz.1.ne'] at hh

theorem inversion_image_inner {R : ℝ} (hR : 0 < R) :
    inversion R '' innerDisk R = exteriorDisk R := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    exact inversion_inner_mem hR hp
  · intro p hp
    refine ⟨inversion R p,inversion_exterior_mem hR hp,?_⟩
    exact inversion_involutive R p hR.ne' ((sq_pos_of_pos hR).trans hp).ne'

theorem jacobian_det (R : ℝ) (p : Plane) (hp : s p.1 p.2 ≠ 0) :
    (jacobian R p).det = -(R^4/(s p.1 p.2)^2) := by
  change LinearMap.det (jacobian R p).toLinearMap = _
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one, Module.Basis.coe_finTwoProd_repr,
    ContinuousLinearMap.coe_coe, jacobian_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_zero, add_zero, zero_add]
  simpa only [pow_two] using determinant R p.1 p.2 hp

theorem jacobian_abs_det (R : ℝ) (p : Plane) (hp : s p.1 p.2 ≠ 0) :
    |(jacobian R p).det| = R^4/(s p.1 p.2)^2 := by
  rw [jacobian_det R p hp, abs_neg, abs_of_nonneg (by positivity)]

theorem kelvin_integrable_iff {R : ℝ} (hR : 0 < R) (f : Plane → ℝ) :
    IntegrableOn f (exteriorDisk R) ↔
      IntegrableOn (fun p => (R^4/(s p.1 p.2)^2)*f (inversion R p)) (innerDisk R) := by
  have hh := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (volume : Measure Plane) (innerDisk_measurable R)
    (fun p hp => (derivative_inversion R p hp.1.ne').hasFDerivWithinAt)
    (inversion_injOn_inner hR) f
  rw [inversion_image_inner hR] at hh
  apply hh.trans
  apply integrableOn_congr_fun
  · intro p hp
    dsimp only
    rw [jacobian_abs_det R p hp.1.ne', smul_eq_mul]
  · exact innerDisk_measurable R

theorem kelvin_integral {R : ℝ} (hR : 0 < R) (f : Plane → ℝ) :
    (∫ p in exteriorDisk R, f p) =
      ∫ p in innerDisk R, (R^4/(s p.1 p.2)^2)*f (inversion R p) := by
  have hh := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure Plane) (innerDisk_measurable R)
    (fun p hp => (derivative_inversion R p hp.1.ne').hasFDerivWithinAt)
    (inversion_injOn_inner hR) f
  rw [inversion_image_inner hR] at hh
  rw [hh]
  apply setIntegral_congr_fun (innerDisk_measurable R)
  intro p hp
  dsimp only
  rw [jacobian_abs_det R p hp.1.ne',smul_eq_mul]

/-- Exact transverse Dirichlet energy after pullback of a gradient vector.
The Jacobian is symmetric, so it acts on the gradient as written. -/
theorem kelvin_transverse_energy {R : ℝ} (hR : 0 < R) (G : Plane → Plane) :
    (∫ p in innerDisk R, s (jacobian R p (G (inversion R p))).1
        (jacobian R p (G (inversion R p))).2) =
      ∫ p in exteriorDisk R, s (G p).1 (G p).2 := by
  rw [kelvin_integral hR]
  apply setIntegral_congr_fun (innerDisk_measurable R)
  intro p hp
  exact jacobian_energy R p (G (inversion R p)) hp.1.ne'

theorem exteriorDisk_measurable (R : ℝ) : MeasurableSet (exteriorDisk R) := by
  have hc : Continuous (fun p : Plane => s p.1 p.2) := by unfold s; fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioi).measurableSet

def kelvinWeight (R : ℝ) (p : Plane) : ℝ := R^4/(s p.1 p.2)^2

theorem weight_nonneg (R : ℝ) (p : Plane) : 0 ≤ kelvinWeight R p := by
  unfold kelvinWeight
  positivity

theorem weight_measurable (R : ℝ) : Measurable (kelvinWeight R) := by
  unfold kelvinWeight s
  fun_prop

theorem weight_inverse {R : ℝ} (hR : 0 < R) {p : Plane} (hp : 0 < s p.1 p.2) :
    kelvinWeight R p*kelvinWeight R (inversion R p) = 1 := by
  unfold kelvinWeight
  rw [show s (inversion R p).1 (inversion R p).2 = R^4/s p.1 p.2 from
    image_norm_sq R p.1 p.2 hp.ne']
  field_simp

theorem weight_le_one_exterior {R : ℝ} (hR : 0 < R) {p : Plane}
    (hp : p ∈ exteriorDisk R) : kelvinWeight R p ≤ 1 := by
  have hs : 0 < s p.1 p.2 := (sq_pos_of_pos hR).trans hp
  unfold kelvinWeight
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hp.le) (add_nonneg hs.le (sq_nonneg R))]

/-- The longitudinal derivative has no transverse Jacobian factor before the
change of variables; the exact exterior weight is R^4/|y|^4. -/
theorem kelvin_longitudinal_integral {R : ℝ} (hR : 0 < R) (f : Plane → ℝ) :
    (∫ p in innerDisk R, f (inversion R p)) =
      ∫ p in exteriorDisk R, kelvinWeight R p*f p := by
  rw [kelvin_integral hR]
  apply setIntegral_congr_fun (innerDisk_measurable R)
  intro p hp
  dsimp only
  change f (inversion R p) = kelvinWeight R p*(kelvinWeight R (inversion R p)*f (inversion R p))
  rw [← mul_assoc,weight_inverse hR hp.1,one_mul]

theorem kelvin_longitudinal_integrable {R : ℝ} (hR : 0 < R) {f : Plane → ℝ}
    (hf : IntegrableOn f (exteriorDisk R)) :
    IntegrableOn (fun p => f (inversion R p)) (innerDisk R) := by
  have hw : IntegrableOn (fun p => kelvinWeight R p*f p) (exteriorDisk R) := by
    apply hf.norm.mono' ((weight_measurable R).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (exteriorDisk_measurable R)] with p hp
    dsimp only [Pi.mul_apply]
    rw [norm_mul,Real.norm_of_nonneg (weight_nonneg R p)]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one_exterior hR hp)
  have hh := (kelvin_integrable_iff hR _).mp hw
  apply hh.congr
  filter_upwards [ae_restrict_mem (innerDisk_measurable R)] with p hp
  change kelvinWeight R p*(kelvinWeight R (inversion R p)*f (inversion R p)) = _
  rw [← mul_assoc,weight_inverse hR hp.1,one_mul]

theorem kelvin_longitudinal_le {R : ℝ} (hR : 0 < R) {f : Plane → ℝ}
    (hf : IntegrableOn f (exteriorDisk R)) (hpos : ∀ p, 0 ≤ f p) :
    (∫ p in innerDisk R, f (inversion R p)) ≤ ∫ p in exteriorDisk R, f p := by
  rw [kelvin_longitudinal_integral hR]
  have hw : IntegrableOn (fun p => kelvinWeight R p*f p) (exteriorDisk R) := by
    apply hf.norm.mono' ((weight_measurable R).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (exteriorDisk_measurable R)] with p hp
    dsimp only [Pi.mul_apply]
    rw [norm_mul,Real.norm_of_nonneg (weight_nonneg R p)]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one_exterior hR hp)
  apply integral_mono_ae hw hf
  filter_upwards [ae_restrict_mem (exteriorDisk_measurable R)] with p hp
  exact mul_le_of_le_one_left (hpos p) (weight_le_one_exterior hR hp)

#print axioms kelvin_longitudinal_integrable
#print axioms kelvin_longitudinal_le
#print axioms jacobian_det
#print axioms kelvin_integrable_iff
#print axioms kelvin_integral
#print axioms kelvin_transverse_energy
end BWork.Kelvin
