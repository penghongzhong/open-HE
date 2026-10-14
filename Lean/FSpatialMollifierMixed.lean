import FSpatialMollifierLp

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint measurability of literal spatial convolution follows from measurable Bochner integration. -/
theorem spatialMollify_joint_stronglyMeasurable (φ : ContDiffBump (0 : Space))
    (f : ℝ → Space → E) (hf : StronglyMeasurable (fun z : ℝ × Space => f z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => spatialMollify φ (f z.1) z.2) := by
  have hm : StronglyMeasurable (fun z : (ℝ × Space) × Space =>
      φ.normed volume z.2 • f z.1.1 (z.1.2 - z.2)) := by
    exact (φ.continuous_normed.comp continuous_snd).stronglyMeasurable.smul
      (hf.comp_measurable (measurable_fst.fst.prodMk (measurable_fst.snd.sub measurable_snd)))
  exact hm.integral_prod_right'

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {p q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] [r.HolderConjugate q]
include r

/-- Genuine mixed-norm convergence for spatially integrable actual fields with finite mixed norm. -/
theorem spatialMollify_mixed_sub_tendsto (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hqTop : q ≠ ∞) {φ : ℕ → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (f : ℝ → Space → E) (hf : StronglyMeasurable (fun z : ℝ × Space => f z.1 z.2))
    (hf1 : ∀ᵐ t ∂volume, Integrable (f t) volume)
    (hfin : mixedNorm volume volume p q f ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume p q
      (fun t x => spatialMollify (φ n) (f t) x - f t x)) atTop (𝓝 0) := by
  have hq0 : q ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le Fact.out)
  have hp0 : p ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le hp)
  have hb : eLpNorm (fun t => eLpNorm (f t) q volume + eLpNorm (f t) q volume) p volume ≠ ∞ := by
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfin, hfin⟩) (eLpNorm_add_le hp)
  apply ennreal_eLpNorm_dominated_zero volume hp0 hpTop
    (fun n => spatial_lp_time_measurable volume volume q hq0 hqTop _
      ((spatialMollify_joint_stronglyMeasurable (φ n) f hf).sub hf).aestronglyMeasurable) hb
  · intro n
    filter_upwards [finite_mixedNorm_ae_slice_memLp volume volume p q hp0 hpTop f hfin, hf1] with t ht ht1
    exact (eLpNorm_sub_le (f := spatialMollify (φ n) (f t)) (g := f t) Fact.out).trans
      (add_le_add (spatialMollify_eLpNorm_le (q := r) hqTop (φ n) ht ht1) le_rfl)
  · filter_upwards [finite_mixedNorm_ae_slice_memLp volume volume p q hp0 hpTop f hfin, hf1] with t ht ht1
    exact spatialMollify_eLpNorm_sub_tendsto (q := r) hqTop hφ ht ht1

#print axioms spatialMollify_mixed_sub_tendsto
end HartreeF.ProfileSpatialSmoothing
