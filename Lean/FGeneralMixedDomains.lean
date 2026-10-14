import FGeneralFrameNorms
import FCrossContinuityBounded

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation CompactCross CrossContinuity

/-- The actual essential-supremum mixed norm also supplies finite spatial slices. -/
theorem finite_top_mixedNorm_ae_slice {E : Type*} [NormedAddCommGroup E]
    (q : ℝ≥0∞) (f : ℝ → Space → E) (hf : mixedNorm volume volume ∞ q f ≠ ∞) :
    ∀ᵐ t ∂volume, MemLp (f t) q volume := by
  have hm := aestronglyMeasurable_of_eLpNorm_ne_top hf
  have hb := ae_le_eLpNormEssSup (f := fun t => eLpNorm (f t) q volume) (μ := (volume : Measure ℝ))
  rw [← eLpNorm_exponent_top hm] at hb
  filter_upwards [hb] with t ht
  exact lt_of_le_of_lt (by simpa only [mixedNorm, enorm_eq_self] using ht) (lt_top_iff_ne_top.mpr hf)

/-- A scalar value and one true weak-gradient coordinate, in the actual critical spaces.
This data record carries literal functions, not an additional analytic interface. -/
structure ScalarProfile (u h : ℝ → Space → ℂ) : Prop where
  value_joint : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2)
  gradient_joint : StronglyMeasurable (fun z : ℝ × Space => h z.1 z.2)
  value_V : mixedNorm volume volume ∞ 6 u ≠ ∞
  value_S : mixedNorm volume volume 10 10 u ≠ ∞
  gradient_W : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h ≠ ∞

theorem ScalarProfile.frame {u h : ℝ → Space → ℂ} (hu : ScalarProfile u h)
    {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ) :
    ScalarProfile (seedFrame a y s (1/2) u) (seedFrame a y s (3/2) h) := by
  refine ⟨seedFrame_joint_stronglyMeasurable a y s _ u hu.value_joint,
    seedFrame_joint_stronglyMeasurable a y s _ h hu.gradient_joint, ?_, ?_, ?_⟩
  · rw [seedFrame_V_invariant ha y s u hu.value_joint.aestronglyMeasurable]
    exact hu.value_V
  · rw [seedFrame_S_invariant ha y s u hu.value_joint.aestronglyMeasurable]
    exact hu.value_S
  · rw [seedFrame_W_invariant ha y s h hu.gradient_joint.aestronglyMeasurable]
    exact hu.gradient_W

theorem ScalarProfile.jointInputs {u U h H v V k K : ℝ → Space → ℂ}
    (hu : ScalarProfile u h) (hU : ScalarProfile U H) (hv : ScalarProfile v k) (hV : ScalarProfile V K) :
    JointInputs u U h H v V k K :=
  ⟨hu.value_joint.aestronglyMeasurable, hU.value_joint.aestronglyMeasurable,
    hu.gradient_joint.aestronglyMeasurable, hU.gradient_joint.aestronglyMeasurable,
    hv.value_joint.aestronglyMeasurable, hV.value_joint.aestronglyMeasurable,
    hv.gradient_joint.aestronglyMeasurable, hV.gradient_joint.aestronglyMeasurable⟩

theorem ScalarProfile.sliceInputs {u U h H v V k K : ℝ → Space → ℂ}
    (hu : ScalarProfile u h) (hU : ScalarProfile U H) (hv : ScalarProfile v k) (hV : ScalarProfile V K) :
    ∀ᵐ t ∂volume, SliceInputs (u t) (U t) (h t) (H t) (v t) (V t) (k t) (K t) := by
  filter_upwards [finite_top_mixedNorm_ae_slice 6 u hu.value_V,
    finite_top_mixedNorm_ae_slice 6 U hU.value_V,
    finite_top_mixedNorm_ae_slice 6 v hv.value_V,
    finite_top_mixedNorm_ae_slice 6 V hV.value_V,
    finite_mixedNorm_ae_slice_memLp volume volume 10 10 (by norm_num) (by norm_num) u hu.value_S,
    finite_mixedNorm_ae_slice_memLp volume volume 10 10 (by norm_num) (by norm_num) U hU.value_S,
    finite_mixedNorm_ae_slice_memLp volume volume 10 10 (by norm_num) (by norm_num) v hv.value_S,
    finite_mixedNorm_ae_slice_memLp volume volume 10 10 (by norm_num) (by norm_num) V hV.value_S,
    finite_mixedNorm_ae_slice_memLp volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num) (by norm_num) h hu.gradient_W,
    finite_mixedNorm_ae_slice_memLp volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num) (by norm_num) H hU.gradient_W,
    finite_mixedNorm_ae_slice_memLp volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num) (by norm_num) k hv.gradient_W,
    finite_mixedNorm_ae_slice_memLp volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (by norm_num) (by norm_num) K hV.gradient_W]
    with t hu6 hU6 hv6 hV6 hu10 hU10 hv10 hV10 hh hH hk hK
  exact ⟨hu6,hU6,hv6,hV6,hu10,hU10,hv10,hV10,hh,hH,hk,hK⟩

/-- Reversing an actual difference preserves the extended mixed norm. -/
theorem mixedNorm_sub_comm {E : Type*} [NormedAddCommGroup E]
    (p q : ℝ≥0∞) (f g : ℝ → Space → E) :
    mixedNorm volume volume p q (fun t x => f t x - g t x) =
      mixedNorm volume volume p q (fun t x => g t x - f t x) := by
  unfold mixedNorm
  congr 1
  funext t
  exact eLpNorm_sub_comm (f t) (g t) q volume

#print axioms finite_top_mixedNorm_ae_slice
#print axioms ScalarProfile.sliceInputs
end HartreeF.GeneralProfileCross
