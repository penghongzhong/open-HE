import Lemma_4_1_PlanePair
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual great-circle parametrization and zeroth/second moments.
No spherical or angular integral identity is an input to these proofs. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace Topology ContDiff
namespace BWork.Angular

abbrev E := EuclideanSpace ℝ (Fin 3)
abbrev Frame := OrthonormalBasis (Fin 3) ℝ E

def circle (e : Frame) (θ : ℝ) : E := Real.cos θ • e 1 + Real.sin θ • e 2

def circleVelocity (e : Frame) (θ : ℝ) : E :=
  -Real.sin θ • e 1 + Real.cos θ • e 2

def tangentProjection (e : Frame) (v : E) : E := v - ⟪e 0,v⟫ • e 0

def circleIntegral (e : Frame) (F : E → ℝ) : ℝ :=
  ∫ θ in 0..2*Real.pi,F (circle e θ)

theorem circle_contDiff (e : Frame) : ContDiff ℝ ∞ (circle e) := by
  exact (Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)

theorem circle_hasDerivAt (e : Frame) (θ : ℝ) :
    HasDerivAt (circle e) (circleVelocity e θ) θ := by
  exact ((Real.hasDerivAt_cos θ).smul_const (e 1)).add
    ((Real.hasDerivAt_sin θ).smul_const (e 2))

theorem circle_normal (e : Frame) (θ : ℝ) : ⟪e 0,circle e θ⟫ = 0 := by
  simp [circle,inner_add_right,inner_smul_right,e.inner_eq_ite]

theorem circle_norm (e : Frame) (θ : ℝ) : ‖circle e θ‖ = 1 := by
  have h : ‖circle e θ‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [circle,inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,
      e.inner_eq_ite]
    norm_num
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (circle e θ)]

theorem circleVelocity_norm (e : Frame) (θ : ℝ) : ‖circleVelocity e θ‖ = 1 := by
  have h : ‖circleVelocity e θ‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [circleVelocity,inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,
      e.inner_eq_ite]
    norm_num
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (circleVelocity e θ)]

theorem tangentProjection_norm_sq (e : Frame) (v : E) :
    ‖tangentProjection e v‖^2 = ‖v‖^2 - ⟪e 0,v⟫^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [tangentProjection,inner_sub_left,inner_sub_right,real_inner_smul_left,
    inner_smul_right,e.inner_eq_ite,ite_true,real_inner_self_eq_norm_sq]
  rw [real_inner_comm v (e 0)]
  ring

theorem transverse_parseval (e : Frame) (v : E) :
    ⟪e 1,v⟫^2 + ⟪e 2,v⟫^2 = ‖tangentProjection e v‖^2 := by
  have h := e.sum_sq_inner_right v
  simp only [Fin.sum_univ_three] at h
  rw [tangentProjection_norm_sq]
  linarith

theorem circle_inner (e : Frame) (v : E) (θ : ℝ) :
    ⟪circle e θ,v⟫ = Real.cos θ*⟪e 1,v⟫ + Real.sin θ*⟪e 2,v⟫ := by
  simp only [circle,inner_add_left,real_inner_smul_left]

theorem circle_zeroth_moment (e : Frame) : circleIntegral e (fun _ => 1) = 2*Real.pi := by
  simp [circleIntegral]

theorem trig_quadratic_integral (a b : ℝ) :
    (∫ θ in 0..2*Real.pi,(Real.cos θ*a + Real.sin θ*b)^2) = Real.pi*(a^2+b^2) := by
  have he (θ : ℝ) : (Real.cos θ*a + Real.sin θ*b)^2 =
      a^2*Real.cos θ^2 + b^2*Real.sin θ^2 + (2*a*b)*(Real.sin θ*Real.cos θ) := by ring
  simp_rw [he]
  have hc : IntervalIntegrable (fun θ => a^2*Real.cos θ^2) volume 0 (2*Real.pi) :=
    (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun θ => b^2*Real.sin θ^2) volume 0 (2*Real.pi) :=
    (continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hcs : IntervalIntegrable (fun θ => (2*a*b)*(Real.sin θ*Real.cos θ)) volume 0 (2*Real.pi) :=
    (continuous_const.mul (Real.continuous_sin.mul Real.continuous_cos)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hc.add hs) hcs,intervalIntegral.integral_add hc hs]
  simp only [intervalIntegral.integral_const_mul,integral_cos_sq,integral_sin_sq,
    integral_sin_mul_cos₁,Real.sin_two_pi,Real.cos_two_pi,Real.sin_zero,Real.cos_zero]
  ring

theorem circle_second_moment (e : Frame) (v : E) :
    circleIntegral e (fun w => ⟪w,v⟫^2) = Real.pi*‖tangentProjection e v‖^2 := by
  unfold circleIntegral
  simp_rw [circle_inner]
  rw [trig_quadratic_integral,transverse_parseval]

theorem tangentProjection_inner (e : Frame) (u v : E) :
    ⟪tangentProjection e u,tangentProjection e v⟫ =
      ⟪u,v⟫-⟪e 0,u⟫*⟪e 0,v⟫ := by
  simp only [tangentProjection,inner_sub_left,inner_sub_right,real_inner_smul_left,
    inner_smul_right,e.inner_eq_ite,ite_true]
  rw [real_inner_comm u (e 0)]
  ring

theorem transverse_bilinear_parseval (e : Frame) (u v : E) :
    ⟪e 1,u⟫*⟪e 1,v⟫ + ⟪e 2,u⟫*⟪e 2,v⟫ =
      ⟪tangentProjection e u,tangentProjection e v⟫ := by
  have h := e.sum_inner_mul_inner u v
  simp only [Fin.sum_univ_three] at h
  rw [← real_inner_comm u (e 0),← real_inner_comm u (e 1),← real_inner_comm u (e 2)] at h
  rw [tangentProjection_inner]
  linarith

theorem trig_bilinear_integral (a b c d : ℝ) :
    (∫ θ in 0..2*Real.pi,(Real.cos θ*a + Real.sin θ*b)*
      (Real.cos θ*c + Real.sin θ*d)) = Real.pi*(a*c+b*d) := by
  have he (θ : ℝ) : (Real.cos θ*a + Real.sin θ*b)*(Real.cos θ*c + Real.sin θ*d) =
      (a*c)*Real.cos θ^2 + (b*d)*Real.sin θ^2 + (a*d+b*c)*(Real.sin θ*Real.cos θ) := by ring
  simp_rw [he]
  have hc : IntervalIntegrable (fun θ => (a*c)*Real.cos θ^2) volume 0 (2*Real.pi) :=
    (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  have hs : IntervalIntegrable (fun θ => (b*d)*Real.sin θ^2) volume 0 (2*Real.pi) :=
    (continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hcs : IntervalIntegrable (fun θ => (a*d+b*c)*(Real.sin θ*Real.cos θ)) volume 0 (2*Real.pi) :=
    (continuous_const.mul (Real.continuous_sin.mul Real.continuous_cos)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hc.add hs) hcs,intervalIntegral.integral_add hc hs]
  simp only [intervalIntegral.integral_const_mul,integral_cos_sq,integral_sin_sq,
    integral_sin_mul_cos₁,Real.sin_two_pi,Real.cos_two_pi,Real.sin_zero,Real.cos_zero]
  ring

theorem circle_bilinear_moment (e : Frame) (u v : E) :
    circleIntegral e (fun w => ⟪w,u⟫*⟪w,v⟫) =
      Real.pi*⟪tangentProjection e u,tangentProjection e v⟫ := by
  unfold circleIntegral
  simp_rw [circle_inner]
  rw [trig_bilinear_integral,transverse_bilinear_parseval]

theorem exists_frame (n : E) (hn : ‖n‖=1) : ∃ e : Frame,e 0=n := by
  have h : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => n)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i=j := by
      apply Subtype.ext
      exact (mem_singleton_iff.mp i.property).trans (mem_singleton_iff.mp j.property).symm
    simp only [hij,ite_true,Set.domRestrict_apply,real_inner_self_eq_norm_sq,hn,one_pow]
  obtain ⟨e,he⟩ := h.exists_orthonormalBasis_extension_of_card_eq (by simp [E])
  exact ⟨e,he 0 (by simp)⟩

#print axioms circle_contDiff
#print axioms circle_hasDerivAt
#print axioms circle_normal
#print axioms circle_norm
#print axioms circleVelocity_norm
#print axioms tangentProjection_norm_sq
#print axioms transverse_parseval
#print axioms circle_inner
#print axioms circle_zeroth_moment
#print axioms trig_quadratic_integral
#print axioms circle_second_moment
#print axioms tangentProjection_inner
#print axioms transverse_bilinear_parseval
#print axioms trig_bilinear_integral
#print axioms circle_bilinear_moment
#print axioms exists_frame
end BWork.Angular
