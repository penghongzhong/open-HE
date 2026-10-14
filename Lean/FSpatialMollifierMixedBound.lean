import FSpatialMollifierMixed

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {p q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] [r.HolderConjugate q]
include r

/-- Spatial smoothing contracts every time norm, including the essential-supremum energy norm. -/
theorem spatialMollify_mixed_le (hqTop : q ≠ ∞) (φ : ContDiffBump (0 : Space))
    (f : ℝ → Space → E) (hf : StronglyMeasurable (fun z : ℝ × Space => f z.1 z.2))
    (hfp : ∀ᵐ t ∂volume, MemLp (f t) q volume)
    (hf1 : ∀ᵐ t ∂volume, Integrable (f t) volume) :
    mixedNorm volume volume p q (fun t => spatialMollify φ (f t)) ≤ mixedNorm volume volume p q f := by
  have hq0 : q ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le Fact.out)
  apply eLpNorm_mono_enorm_ae (spatial_lp_time_measurable volume volume q hq0 hqTop _
    (spatialMollify_joint_stronglyMeasurable φ f hf).aestronglyMeasurable)
  filter_upwards [hfp, hf1] with t ht ht1
  simpa only [enorm_eq_self] using spatialMollify_eLpNorm_le (q := r) hqTop φ ht ht1

#print axioms spatialMollify_mixed_le
end HartreeF.ProfileSpatialSmoothing
