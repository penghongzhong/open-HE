import FAffineMeasurePushforward
import FWeakSourceAffinePullback

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.AffineL1Source
open CriticalAffine AffineMixed SobolevStretch

/-- A proper affine homeomorphism preserves the actual local-L1 domain. -/
theorem affine_locallyIntegrable {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} (hf : LocallyIntegrable f volume)
    {a : ℝ} (ha : 0<a) (b : Space) :
    LocallyIntegrable (f ∘ affine a b) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hmap : Measure.map (affine a b) (volume.restrict K)=
      ENNReal.ofReal ((a^3)⁻¹) • volume.restrict ((affine a b) '' K) := by
    have h := (affineHomeomorph ha.ne' b).toMeasurableEquiv.restrict_map volume ((affine a b) '' K)
    change (Measure.map (affine a b) volume).restrict ((affine a b) '' K)=
      Measure.map (affine a b) (volume.restrict ((affine a b) ⁻¹' ((affine a b) '' K))) at h
    have hinj : Function.Injective (affine a b) := (affineHomeomorph ha.ne' b).injective
    rw [hinj.preimage_image] at h
    rw [← h,affine_map_volume ha b,Measure.restrict_smul]
  apply (affineHomeomorph ha.ne' b).toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mp
  change Integrable f (Measure.map (affine a b) (volume.restrict K))
  rw [hmap]
  exact (hf.integrableOn_isCompact (hK.image (affineHomeomorph ha.ne' b).continuous)).smul_measure
    ENNReal.ofReal_ne_top

/-- Pull back the stored local-L1 weak-gradient fields themselves. No global
Lp, scalar time2 or extra slice-domain assumption is required. -/
theorem hasWeakGradient_affine_local {f : Space → ℝ} {G : Space → Space}
    (h : HasWeakGradient f G) {a : ℝ} (ha : 0<a) (b : Space) (k : ℝ) :
    HasWeakGradient (fun x => k*f (affine a b x)) (fun x => (k*a) • G (affine a b x)) := by
  refine ⟨(affine_locallyIntegrable h.function_local ha b).smul k,
    (affine_locallyIntegrable h.gradient_local ha b).smul (k*a), ?_⟩
  intro v φ hφ hc
  let ψ : Space → ℝ := fun y => φ (a⁻¹ • (y-b))
  have ht := inverse_affine_test_class ha b hφ hc
  have hw := h.integration_by_parts (a • v) ψ ht.1 ht.2
  have hj1 := affine_integral ha b (fun y => f y*fderiv ℝ ψ y (a • v))
  have hj2 := affine_integral ha b (fun y => inner ℝ (G y) (a • v)*ψ y)
  have hd (x : Space) : fderiv ℝ ψ (affine a b x) (a • v)=fderiv ℝ φ x v := by
    rw [inverse_affine_test_derivative ha b hφ]
    simp [affine,smul_smul,ha.ne']
  have hv (x : Space) : ψ (affine a b x)=φ x := by
    simp [ψ,affine,smul_smul,ha.ne']
  simp only [hd,smul_eq_mul] at hj1
  simp only [hv,smul_eq_mul] at hj2
  have he : (∫ x, f (affine a b x)*fderiv ℝ φ x v)=
      -(∫ x, inner ℝ (G (affine a b x)) (a • v)*φ x) := by
    rw [hj1,hw,mul_neg,← hj2]
  have hg (x : Space) : inner ℝ ((k*a) • G (affine a b x)) v=
      k*inner ℝ (G (affine a b x)) (a • v) := by
    simp only [real_inner_smul_left,real_inner_smul_right]
    ring
  simp only [hg,mul_assoc,integral_const_mul,he,mul_neg]

#print axioms affine_locallyIntegrable
#print axioms hasWeakGradient_affine_local
end HartreeF.AffineL1Source
