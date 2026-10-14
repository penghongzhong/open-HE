import ComplexWeakCutoff
import SobolevKineticStretch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ComplexIMS
open SobolevStretch WeakCutoffLp

/-- A literal smooth angle which is pi/2 outside a finite ball. -/
structure AngleCutoff (θ : Space → ℝ) (R : ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ENat) θ
  nonneg : ∀ x, 0 ≤ θ x
  le_half_pi : ∀ x, θ x ≤ Real.pi / 2
  radius_pos : 0 < R
  outside : ∀ x, R ≤ ‖x‖ → θ x = Real.pi / 2

def core (θ : Space → ℝ) (u : Space → ℂ) (x : Space) : ℂ :=
  Real.cos (θ x) • u x

def tail (θ : Space → ℝ) (u : Space → ℂ) (x : Space) : ℂ :=
  Real.sin (θ x) • u x

def coreGradient (θ f : Space → ℝ) (G : Space → Space) (x : Space) : Space :=
  Real.cos (θ x) • G x - (Real.sin (θ x) * f x) • gradient θ x

def tailGradient (θ f : Space → ℝ) (G : Space → Space) (x : Space) : Space :=
  Real.sin (θ x) • G x + (Real.cos (θ x) * f x) • gradient θ x

theorem compact_of_zero_outside {E : Type*} [Zero E] {f : Space → E} {R : ℝ}
    (hf : ∀ x, R ≤ ‖x‖ → f x = 0) : HasCompactSupport f := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Space) R) isClosed_closedBall
  intro x hx
  apply hf
  have : ¬ ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
  exact (lt_of_not_ge this).le

theorem AngleCutoff.cos_compact {θ : Space → ℝ} {R : ℝ} (h : AngleCutoff θ R) :
    HasCompactSupport (fun x => Real.cos (θ x)) := by
  apply compact_of_zero_outside (R := R)
  intro x hx
  rw [h.outside x hx, Real.cos_pi_div_two]

theorem AngleCutoff.gradient_compact {θ : Space → ℝ} {R : ℝ} (h : AngleCutoff θ R) :
    HasCompactSupport (gradient θ) := by
  have hc : HasCompactSupport (fun x => θ x - Real.pi / 2) := by
    apply compact_of_zero_outside (R := R)
    intro x hx
    rw [h.outside x hx, sub_self]
  have hg := cutoff_gradient_hasCompactSupport hc
  have he : gradient (fun x => θ x - Real.pi / 2) = gradient θ := by
    funext x
    simp only [gradient, fderiv_sub_const]
  rwa [he] at hg

theorem AngleCutoff.gradient_memLp {θ : Space → ℝ} {R : ℝ}
    (h : AngleCutoff θ R) (p : ℝ≥0∞) : MemLp (gradient θ) p volume :=
  (smooth_gradient_continuous h.smooth).memLp_of_hasCompactSupport h.gradient_compact

theorem angle_gradient_cos {θ : Space → ℝ} (hθ : ContDiff ℝ (⊤ : ENat) θ)
    (x : Space) : gradient (fun y => Real.cos (θ y)) x =
      -Real.sin (θ x) • gradient θ x := by
  simp only [gradient, fderiv_cos (hθ.differentiable (by simp) x), map_smul]

theorem angle_gradient_sin {θ : Space → ℝ} (hθ : ContDiff ℝ (⊤ : ENat) θ)
    (x : Space) : gradient (fun y => Real.sin (θ y)) x =
      Real.cos (θ x) • gradient θ x := by
  simp only [gradient, fderiv_sin (hθ.differentiable (by simp) x), map_smul]

theorem cos_memLp_top {θ : Space → ℝ} (hθ : Continuous θ) :
    MemLp (fun x => Real.cos (θ x)) ∞ volume := by
  apply memLp_top_of_bound ((Real.continuous_cos.comp hθ).aestronglyMeasurable) 1
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using Real.abs_cos_le_one (θ x))

theorem sin_memLp_top {θ : Space → ℝ} (hθ : Continuous θ) :
    MemLp (fun x => Real.sin (θ x)) ∞ volume := by
  apply memLp_top_of_bound ((Real.continuous_sin.comp hθ).aestronglyMeasurable) 1
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using Real.abs_sin_le_one (θ x))

theorem core_eq_zero_outside {θ : Space → ℝ} {R : ℝ} (h : AngleCutoff θ R)
    (u : Space → ℂ) {x : Space} (hx : R ≤ ‖x‖) : core θ u x = 0 := by
  simp only [core, h.outside x hx, Real.cos_pi_div_two, zero_smul]

theorem tail_eq_self_outside {θ : Space → ℝ} {R : ℝ} (h : AngleCutoff θ R)
    (u : Space → ℂ) {x : Space} (hx : R ≤ ‖x‖) : tail θ u x = u x := by
  simp only [tail, h.outside x hx, Real.sin_pi_div_two, one_smul]

theorem norm_sq_split (θ : Space → ℝ) (u : Space → ℂ) (x : Space) :
    ‖core θ u x‖^2 + ‖tail θ u x‖^2 = ‖u x‖^2 := by
  simp only [core, tail, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (θ x)]

end HartreeF.ComplexIMS
