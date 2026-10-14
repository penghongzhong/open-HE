import FSpatialMollifierSupport
import FSpatialMollifierMixedBound
import FSpatialSobolevCoupling

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Every slice of a compactly supported spacetime field has compact spatial support. -/
theorem compact_spacetime_slice {f : ℝ → Space → E}
    (hc : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2)) (t : ℝ) :
    HasCompactSupport (f t) := by
  apply HasCompactSupport.intro (hc.image continuous_snd)
  intro x hx
  by_contra hn
  exact hx ⟨(t,x), subset_closure hn, rfl⟩

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {p q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] [r.HolderConjugate q]
include r

/-- Compact support supplies every L1 slice needed for genuine mixed-norm smoothing convergence. -/
theorem spatialMollify_compact_mixed_sub_tendsto (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hqTop : q ≠ ∞) {φ : ℕ → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (f : ℝ → Space → E) (hf : StronglyMeasurable (fun z : ℝ × Space => f z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2))
    (hfin : mixedNorm volume volume p q f ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume p q
      (fun t x => spatialMollify (φ n) (f t) x - f t x)) atTop (𝓝 0) := by
  apply spatialMollify_mixed_sub_tendsto (r := r) hp hpTop hqTop hφ f hf _ hfin
  filter_upwards [finite_mixedNorm_ae_slice_memLp volume volume p q
    (ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le hp)) hpTop f hfin] with t ht
  exact integrable_of_memLp_compact Fact.out ht (compact_spacetime_slice hc t)

/-- Compact spatial slices make the mixed-norm contraction apply, also at time exponent infinity. -/
theorem spatialMollify_compact_mixed_le (hqTop : q ≠ ∞) (φ : ContDiffBump (0 : Space))
    (f : ℝ → Space → E) (hf : StronglyMeasurable (fun z : ℝ × Space => f z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2))
    (hfp : ∀ᵐ t ∂volume, MemLp (f t) q volume) :
    mixedNorm volume volume p q (fun t => spatialMollify φ (f t)) ≤ mixedNorm volume volume p q f := by
  apply spatialMollify_mixed_le (r := r) hqTop φ f hf hfp
  exact hfp.mono fun t ht => integrable_of_memLp_compact Fact.out ht (compact_spacetime_slice hc t)

#print axioms compact_spacetime_slice
#print axioms spatialMollify_compact_mixed_sub_tendsto
#print axioms spatialMollify_compact_mixed_le
end HartreeF.ProfileSpatialSmoothing
