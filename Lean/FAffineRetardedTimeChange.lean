import FAffineMeasurePushforward

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.AffinePath
open AffineMixed

theorem timeAffine_preimage_Iio {a : ℝ} (ha : 0<a) (c t : ℝ) :
    (timeAffine a c) ⁻¹' Iio (timeAffine a c t)=Iio t := by
  ext s
  simp only [mem_preimage,mem_Iio,timeAffine,add_lt_add_iff_right,
    mul_lt_mul_iff_right₀ (pow_pos ha 2)]

/-- Exact Bochner time change on the restricted source set. -/
theorem timeAffine_integral_restrict {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0<a) (c : ℝ) (S : Set ℝ) (f : ℝ → F) :
    (∫ s in (timeAffine a c) ⁻¹' S, f (timeAffine a c s))=
      (a^2)⁻¹ • ∫ r in S, f r := by
  have h := (timeAffineHomeomorph ha c).toMeasurableEquiv.measurableEmbedding.integral_map
    (μ := volume.restrict ((timeAffine a c) ⁻¹' S)) f
  change (∫ r, f r ∂Measure.map (timeAffine a c)
    (volume.restrict ((timeAffine a c) ⁻¹' S)))=
    ∫ s in (timeAffine a c) ⁻¹' S, f (timeAffine a c s) at h
  rw [timeAffine_map_restrict ha c S,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg a))] at h
  exact h.symm

/-- The literal past-domain map, retaining the positive time orientation. -/
theorem timeAffine_integral_past {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℝ} (ha : 0<a) (c A B t : ℝ) (f : ℝ → F) :
    (∫ s in Icc A B ∩ Iio t, f (timeAffine a c s))=
      (a^2)⁻¹ • ∫ r in Icc (timeAffine a c A) (timeAffine a c B) ∩ Iio (timeAffine a c t), f r := by
  have h := timeAffine_integral_restrict ha c
    (Icc (timeAffine a c A) (timeAffine a c B) ∩ Iio (timeAffine a c t)) f
  rw [preimage_inter,timeAffine_preimage_Icc ha c A B,timeAffine_preimage_Iio ha c t] at h
  exact h

#print axioms timeAffine_preimage_Iio
#print axioms timeAffine_integral_restrict
#print axioms timeAffine_integral_past
end HartreeF.AffinePath
