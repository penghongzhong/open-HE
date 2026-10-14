import FAffineMixedNormIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.AffineMixed
open TimeHolder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {a : ℝ} (ha : 0<a) (b : Space) (c : ℝ) (S : Set ℝ) (f : ℝ → Space → E)
  (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) ((volume.restrict S).prod volume))

include ha hf

theorem parabolic_S_invariant :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume 10 10 (parabolicField a b c (1/2) f)=
      mixedNorm (volume.restrict S) volume 10 10 f := by
  have h := mixedNorm_parabolicField ha b c (1/2) S 10 10 (by norm_num) (by norm_num) f hf
  norm_num [reciprocalExponent] at h
  exact h

theorem parabolic_energy_value_invariant :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume ∞ 6 (parabolicField a b c (1/2) f)=
      mixedNorm (volume.restrict S) volume ∞ 6 f := by
  have h := mixedNorm_parabolicField ha b c (1/2) S ∞ 6 (by norm_num) (by norm_num) f hf
  norm_num [reciprocalExponent] at h
  exact h

theorem parabolic_W_invariant :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume 10 (ENNReal.ofReal (30/13:ℝ))
      (parabolicField a b c (3/2) f)=
      mixedNorm (volume.restrict S) volume 10 (ENNReal.ofReal (30/13:ℝ)) f := by
  have h := mixedNorm_parabolicField ha b c (3/2) S 10 (ENNReal.ofReal (30/13:ℝ)) (by norm_num) (by norm_num) f hf
  norm_num [reciprocalExponent] at h
  exact h

theorem parabolic_energy_gradient_invariant :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume ∞ 2 (parabolicField a b c (3/2) f)=
      mixedNorm (volume.restrict S) volume ∞ 2 f := by
  have h := mixedNorm_parabolicField ha b c (3/2) S ∞ 2 (by norm_num) (by norm_num) f hf
  norm_num [reciprocalExponent] at h
  exact h

theorem parabolic_N_invariant :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume 2 (ENNReal.ofReal (6/5:ℝ))
      (parabolicField a b c (7/2) f)=
      mixedNorm (volume.restrict S) volume 2 (ENNReal.ofReal (6/5:ℝ)) f := by
  have h := mixedNorm_parabolicField ha b c (7/2) S 2 (ENNReal.ofReal (6/5:ℝ)) (by norm_num) (by norm_num) f hf
  norm_num [reciprocalExponent] at h
  exact h

/-- The active scalar-L1 source is finite under rescaling, but not invariant. -/
theorem parabolic_scalar_L1_scaling :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume 1 (ENNReal.ofReal (6/5:ℝ))
      (parabolicField a b c (5/2) f)=
      ENNReal.ofReal (a^(-2:ℝ))*mixedNorm (volume.restrict S) volume 1 (ENNReal.ofReal (6/5:ℝ)) f := by
  have h := mixedNorm_parabolicField ha b c (5/2) S 1 (ENNReal.ofReal (6/5:ℝ)) (by norm_num) (by norm_num) f hf
  norm_num [reciprocalExponent] at h ⊢
  exact h

/-- Optional identity for the older scalar-time2 space; it is not a premise in
the active scalar-L1 source consumer below. -/
theorem legacy_scalar_L2_scaling :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume 2 (ENNReal.ofReal (6/5:ℝ))
      (parabolicField a b c (5/2) f)=
      ENNReal.ofReal (a^(-1:ℝ))*mixedNorm (volume.restrict S) volume 2 (ENNReal.ofReal (6/5:ℝ)) f := by
  have h := mixedNorm_parabolicField ha b c (5/2) S 2 (ENNReal.ofReal (6/5:ℝ)) (by norm_num) (by norm_num) f hf
  norm_num [reciprocalExponent] at h
  exact h

#print axioms parabolic_S_invariant
#print axioms parabolic_energy_value_invariant
#print axioms parabolic_W_invariant
#print axioms parabolic_energy_gradient_invariant
#print axioms parabolic_N_invariant
#print axioms parabolic_scalar_L1_scaling
#print axioms legacy_scalar_L2_scaling
end HartreeF.AffineMixed
