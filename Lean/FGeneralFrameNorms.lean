import FCompactCrossFourTerms
import FActualProfileCompactApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder CompactCross AffineMixed CriticalAffine

/-- The literal physical frame is linear on actual scalar fields. -/
theorem seedFrame_sub (a : ℝ) (y : Space) (s w : ℝ) (f g : ℝ → Space → ℂ) :
    seedFrame a y s w (fun t x => f t x - g t x) =
      (fun t x => seedFrame a y s w f t x - seedFrame a y s w g t x) := by
  funext t x
  simp only [seedFrame, parabolicField, smul_sub]

theorem seedFrame_joint_stronglyMeasurable (a : ℝ) (y : Space) (s w : ℝ)
    (f : ℝ → Space → ℂ) (hf : StronglyMeasurable (fun z : ℝ × Space => f z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => seedFrame a y s w f z.1 z.2) := by
  have hc : Continuous (fun z : ℝ × Space =>
      (timeAffine a⁻¹ s z.1, affine a⁻¹ (-(a⁻¹ • y)) z.2)) := by
    unfold timeAffine affine
    fun_prop
  exact (hf.comp_measurable hc.measurable).const_smul _

variable {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) (f : ℝ → Space → ℂ)
  (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
include ha hf

/-- Critical value covariance in the original physical frame convention. -/
theorem seedFrame_S_invariant : mixedNorm volume volume 10 10 (seedFrame a y s (1/2) f) =
    mixedNorm volume volume 10 10 f := by
  have h := mixedNorm_parabolicField (inv_pos.mpr ha) (-(a⁻¹ • y)) s (1/2) Set.univ
    10 10 (by norm_num) (by norm_num) f (by simpa using hf)
  norm_num [reciprocalExponent] at h
  exact h

theorem seedFrame_V_invariant : mixedNorm volume volume ∞ 6 (seedFrame a y s (1/2) f) =
    mixedNorm volume volume ∞ 6 f := by
  have h := mixedNorm_parabolicField (inv_pos.mpr ha) (-(a⁻¹ • y)) s (1/2) Set.univ
    ∞ 6 (by norm_num) (by norm_num) f (by simpa using hf)
  norm_num [reciprocalExponent] at h
  exact h

/-- The genuine derivative weight is 3/2, giving critical W covariance. -/
theorem seedFrame_W_invariant :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (seedFrame a y s (3/2) f) =
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) f := by
  have h := mixedNorm_parabolicField (inv_pos.mpr ha) (-(a⁻¹ • y)) s (3/2) Set.univ
    10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num) (by norm_num) f (by simpa using hf)
  norm_num [reciprocalExponent] at h
  exact h

theorem seedFrame_E_invariant : mixedNorm volume volume ∞ 2 (seedFrame a y s (3/2) f) =
    mixedNorm volume volume ∞ 2 f := by
  have h := mixedNorm_parabolicField (inv_pos.mpr ha) (-(a⁻¹ • y)) s (3/2) Set.univ
    ∞ 2 (by norm_num) (by norm_num) f (by simpa using hf)
  norm_num [reciprocalExponent] at h
  exact h

/-- Frame-invariant S approximation error, before choosing any orthogonality index. -/
theorem seedFrame_S_error (g : ℝ → Space → ℂ)
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume 10 10
      (fun t x => seedFrame a y s (1/2) f t x - seedFrame a y s (1/2) g t x) =
      mixedNorm volume volume 10 10 (fun t x => f t x - g t x) := by
  rw [← seedFrame_sub]
  exact seedFrame_S_invariant ha y s _ (hf.sub hg)

theorem seedFrame_W_error (g : ℝ → Space → ℂ)
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t x => seedFrame a y s (3/2) f t x - seedFrame a y s (3/2) g t x) =
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (fun t x => f t x - g t x) := by
  rw [← seedFrame_sub]
  exact seedFrame_W_invariant ha y s _ (hf.sub hg)

#print axioms seedFrame_S_error
#print axioms seedFrame_W_error
end HartreeF.GeneralProfileCross
