import FAffineMixedNormIdentity
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.AffineL1Source
open CriticalAffine AffineMixed

theorem timeAffine_quasiMeasurePreserving {a : ℝ} (ha : 0<a) (c : ℝ) (I : Set ℝ) :
    Measure.QuasiMeasurePreserving (timeAffine a c)
      (volume.restrict ((timeAffine a c) ⁻¹' I)) (volume.restrict I) := by
  refine ⟨(timeAffineHomeomorph ha c).measurable,?_⟩
  rw [timeAffine_map_restrict ha c I]
  exact Measure.smul_absolutelyContinuous

/-- Literal product pushforward on the actual restricted source time set. -/
theorem parabolicJoint_map_measure {a : ℝ} (ha : 0<a) (b : Space) (c : ℝ) (I : Set ℝ) :
    Measure.map (Prod.map (timeAffine a c) (affine a b))
      ((volume.restrict ((timeAffine a c) ⁻¹' I)).prod volume)=
      ENNReal.ofReal ((a^2)⁻¹) • (ENNReal.ofReal ((a^3)⁻¹) •
        ((volume.restrict I).prod (volume : Measure Space))) := by
  have ht : Measurable (timeAffine a c) := (timeAffineHomeomorph ha c).measurable
  have hx : Measurable (affine a b) := (affineHomeomorph ha.ne' b).measurable
  rw [← Measure.map_prod_map _ _ ht hx,timeAffine_map_restrict ha c I,
    affine_map_volume ha b,Measure.prod_smul_left,Measure.prod_smul_right]

/-- The same literal spacetime representatives used in the norm identities
are jointly measurable after pullback; no transformed field is supplied. -/
theorem parabolicField_jointly_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {a : ℝ} (ha : 0<a) (b : Space) (c k : ℝ) (I : Set ℝ) (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) ((volume.restrict I).prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => parabolicField a b c k f z.1 z.2)
      ((volume.restrict ((timeAffine a c) ⁻¹' I)).prod volume) := by
  have hp : AEStronglyMeasurable ((fun z : ℝ × Space => f z.1 z.2) ∘
      Prod.map (timeAffine a c) (affine a b))
      ((volume.restrict ((timeAffine a c) ⁻¹' I)).prod volume) := by
    apply ((timeAffineHomeomorph ha c).toMeasurableEquiv.prodCongr
      (affineHomeomorph ha.ne' b).toMeasurableEquiv).measurableEmbedding.aestronglyMeasurable_map_iff.mp
    change AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2)
      (Measure.map (Prod.map (timeAffine a c) (affine a b))
        ((volume.restrict ((timeAffine a c) ⁻¹' I)).prod volume))
    rw [parabolicJoint_map_measure ha b c I]
    exact (hf.smul_measure _).smul_measure _
  exact hp.const_smul (a^k)

#print axioms timeAffine_quasiMeasurePreserving
#print axioms parabolicJoint_map_measure
#print axioms parabolicField_jointly_measurable
end HartreeF.AffineL1Source
