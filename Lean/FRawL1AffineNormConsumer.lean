import FCriticalAffineMixedNorms
import FRawL1GradientSource

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.AffineMixed
open TimeHolder RawStabilityInputs IntervalTimeTransport

/-- The current raw source interface needs only local scalar L1. Its actual
compact-source domains survive positive-orientation affine time transport.
There is no global scalar-norm or scalar-time2 assumption. -/
theorem raw_source_local_scaled_norms {I : Set ℝ}
    {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (h : RawSpatialGradientSource I e G) {a : ℝ} (ha : 0<a)
    (b : Space) (c A B : ℝ) (hAB : A≤B)
    (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆ I) :
    mixedNorm (localMeasure A B) volume 1 sourceExponent (parabolicField a b c (5/2) e)=
      ENNReal.ofReal (a^(-2:ℝ))*mixedNorm
        (localMeasure (timeAffine a c A) (timeAffine a c B)) volume 1 sourceExponent e ∧
    mixedNorm (localMeasure A B) volume 2 sourceExponent (parabolicField a b c (7/2) G)=
      mixedNorm (localMeasure (timeAffine a c A) (timeAffine a c B)) volume 2 sourceExponent G ∧
    mixedNorm (localMeasure A B) volume 1 sourceExponent (parabolicField a b c (5/2) e)≠∞ ∧
    mixedNorm (localMeasure A B) volume 2 sourceExponent (parabolicField a b c (7/2) G)≠∞ := by
  have ht : timeAffine a c A≤timeAffine a c B := by
    unfold timeAffine
    exact add_le_add_left (mul_le_mul_of_nonneg_left hAB (sq_nonneg a)) c
  have hv := parabolic_scalar_L1_scaling ha b c
    (Icc (timeAffine a c A) (timeAffine a c B)) e (h.value_local_joint hI)
  have hg := parabolic_N_invariant ha b c
    (Icc (timeAffine a c A) (timeAffine a c B)) G (h.gradient_local_joint hI)
  rw [timeAffine_preimage_Icc ha c A B] at hv hg
  refine ⟨hv,hg,?_,?_⟩
  · rw [hv]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (h.value_local ht hI)
  · rw [hg]
    exact h.gradient_local_finite hI

#print axioms raw_source_local_scaled_norms
end HartreeF.AffineMixed
