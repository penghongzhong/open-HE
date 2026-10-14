import Lemma_4_1_GreatCircle
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Actual orthonormal coordinates: volume preservation, derivatives, and
identification of the paper's transverse/longitudinal energies. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace Topology ContDiff
namespace BWork.Angular
open Kelvin

def packLinear : Space ≃ₗ[ℝ] E where
  toFun z := WithLp.toLp 2 ![z.1,z.2.1,z.2.2]
  invFun x := (x 0,(x 1,x 2))
  left_inv _ := rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl

def pack : Space ≃L[ℝ] E := packLinear.toContinuousLinearEquiv

def unpackMeasurable : E ≃ᵐ Space :=
  ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ Kelvin.Plane))

theorem unpackMeasurable_apply (x : E) : unpackMeasurable x = (x 0,(x 1,x 2)) := rfl

theorem pack_measurable_inverse : (pack : Space → E) = unpackMeasurable.symm := by
  funext z
  apply unpackMeasurable.injective
  rw [unpackMeasurable.apply_symm_apply]
  rfl

theorem pack_preserving : MeasurePreserving (pack : Space → E) := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)))
  have hu : MeasurePreserving unpackMeasurable := h
  rw [pack_measurable_inverse]
  exact hu.symm

def frameMap (e : Frame) : Space ≃L[ℝ] E :=
  pack.trans e.repr.symm.toContinuousLinearEquiv

theorem frameMap_apply (e : Frame) (z : Space) :
    frameMap e z = z.1 • e 0 + z.2.1 • e 1 + z.2.2 • e 2 := by
  have h := e.sum_repr_symm (pack z)
  simp only [Fin.sum_univ_three] at h
  exact h.symm

theorem frameMap_preserving (e : Frame) : MeasurePreserving (frameMap e : Space → E) :=
  e.measurePreserving_repr_symm.comp pack_preserving

theorem frameMap_integral (e : Frame) (F : E → ℝ) :
    (∫ z : Space,F (frameMap e z)) = ∫ x : E,F x := by
  have h : MeasurePreserving (frameMap e).toHomeomorph.toMeasurableEquiv := frameMap_preserving e
  exact h.integral_comp' F

def inFrame (e : Frame) (g : E → ℝ) : Space → ℝ := g ∘ frameMap e

theorem inFrame_contDiff (e : Frame) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (inFrame e g) := hg.comp (frameMap e).contDiff

theorem inFrame_compact (e : Frame) {g : E → ℝ} (hc : HasCompactSupport g) :
    HasCompactSupport (inFrame e g) := hc.comp_homeomorph (frameMap e).toHomeomorph

theorem inFrame_fderiv (e : Frame) {g : E → ℝ} (hg : Differentiable ℝ g) (z : Space) :
    fderiv ℝ (inFrame e g) z = (fderiv ℝ g (frameMap e z)).comp (frameMap e).toContinuousLinearMap := by
  exact ((hg (frameMap e z)).hasFDerivAt.comp z (frameMap e).hasFDerivAt).fderiv

theorem inFrame_longitudinal (e : Frame) {g : E → ℝ} (hg : Differentiable ℝ g) (z : Space) :
    longitudinalDerivative (inFrame e g) z = fderiv ℝ g (frameMap e z) (e 0) := by
  unfold longitudinalDerivative
  rw [inFrame_fderiv e hg z,ContinuousLinearMap.comp_apply]
  have he : frameMap e (1,0) = e 0 := by simp [frameMap_apply]
  exact congrArg (fderiv ℝ g (frameMap e z)) he

theorem inFrame_transverse (e : Frame) {g : E → ℝ} (hg : Differentiable ℝ g) (z : Space) :
    transverseDensity (fderiv ℝ (inFrame e g)) z =
      (fderiv ℝ g (frameMap e z) (e 1))^2+(fderiv ℝ g (frameMap e z) (e 2))^2 := by
  unfold transverseDensity transverseGradient s
  rw [inFrame_fderiv e hg z]
  simp only [ContinuousLinearMap.comp_apply]
  have h₁ : frameMap e (0,(1,0)) = e 1 := by simp [frameMap_apply]
  have h₂ : frameMap e (0,(0,1)) = e 2 := by simp [frameMap_apply]
  change (fderiv ℝ g (frameMap e z) (frameMap e (0,(1,0))))^2+
    (fderiv ℝ g (frameMap e z) (frameMap e (0,(0,1))))^2 = _
  rw [h₁,h₂]

theorem directional_parseval (e : Frame) (g : E → ℝ) (x : E) :
    (fderiv ℝ g x (e 0))^2+(fderiv ℝ g x (e 1))^2+(fderiv ℝ g x (e 2))^2 =
      ‖gradient g x‖^2 := by
  have h := e.sum_sq_inner_left (gradient g x)
  simpa only [Fin.sum_univ_three,inner_gradient_left] using h

theorem transverse_energy_identity (e : Frame) {g : E → ℝ} (hg : Differentiable ℝ g) :
    (∫ z : Space,transverseDensity (fderiv ℝ (inFrame e g)) z) =
      ∫ x : E,‖tangentProjection e (gradient g x)‖^2 := by
  have hpoint (z : Space) : transverseDensity (fderiv ℝ (inFrame e g)) z =
      ‖tangentProjection e (gradient g (frameMap e z))‖^2 := by
    rw [inFrame_transverse e hg z,← transverse_parseval]
    simp only [inner_gradient_right,conj_trivial]
  simp_rw [hpoint]
  exact frameMap_integral e (fun x => ‖tangentProjection e (gradient g x)‖^2)

#print axioms unpackMeasurable_apply
#print axioms pack_measurable_inverse
#print axioms pack_preserving
#print axioms frameMap_apply
#print axioms frameMap_preserving
#print axioms frameMap_integral
#print axioms inFrame_contDiff
#print axioms inFrame_compact
#print axioms inFrame_fderiv
#print axioms inFrame_longitudinal
#print axioms inFrame_transverse
#print axioms directional_parseval
#print axioms transverse_energy_identity
end BWork.Angular
