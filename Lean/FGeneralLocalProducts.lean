import FLocalProductFrameError
import FLocalCompactProducts

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalProfileProducts
open TimeHolder ProfileApproximation ProfileSpatialSmoothing GeneralProfileCross CompactCross

/-- Local value/value and value/derivative products vanish along the original filter.
One common approximation index is selected before both physical frames. -/
theorem scalar_pair_PQ_orthogonality {ι : Type*} {l : Filter ι}
    {u h v k : ℝ → Space → ℂ} (A : ScalarCompactApproximation u h)
    (B : ScalarCompactApproximation v k)
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => localProductNorm 5 (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (1/2) v)) l (𝓝 0) ∧
    Tendsto (fun i => localProductNorm (ENNReal.ofReal (15/8 : ℝ))
      (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (3/2) k)) l (𝓝 0) := by
  obtain ⟨C,hCf,hC⟩ := bounded_frame_PQ_error A B
  have he : Tendsto (fun n => C*smoothingPrecision n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul smoothingPrecision_tendsto
      (a := C) (Or.inr hCf)
  constructor
  · apply tendsto_zero_of_uniform_approximation he (fun n =>
      compact_P_orthogonality (A.value_continuous n) (B.value_continuous n)
        (A.value_compact n) (B.value_compact n) ha hb horth)
    intro n i
    have h1 := A.profile.frame (ha i) (y i) (s i)
    have h2 := B.profile.frame (hb i) (z i) (r i)
    have h3 := (A.approximate_profile n).frame (ha i) (y i) (s i)
    have h4 := (B.approximate_profile n).frame (hb i) (z i) (r i)
    exact (localProductNorm_le_error_add (by norm_num) (by norm_num) _ _ _ _
      h1.value_joint.aestronglyMeasurable h3.value_joint.aestronglyMeasurable
      h2.value_joint.aestronglyMeasurable h4.value_joint.aestronglyMeasurable).trans
      (add_le_add (hC n (a i) (b i) (y i) (z i) (s i) (r i) (ha i) (hb i)).1 le_rfl)
  · apply tendsto_zero_of_uniform_approximation he (fun n =>
      compact_Q_orthogonality (A.value_continuous n) (B.gradient_continuous n)
        (A.value_compact n) (B.gradient_compact n) ha hb horth)
    intro n i
    have h1 := A.profile.frame (ha i) (y i) (s i)
    have h2 := B.profile.frame (hb i) (z i) (r i)
    have h3 := (A.approximate_profile n).frame (ha i) (y i) (s i)
    have h4 := (B.approximate_profile n).frame (hb i) (z i) (r i)
    exact (localProductNorm_le_error_add (by norm_num) (by norm_num) _ _ _ _
      h1.value_joint.aestronglyMeasurable h3.value_joint.aestronglyMeasurable
      h2.gradient_joint.aestronglyMeasurable h4.gradient_joint.aestronglyMeasurable).trans
      (add_le_add (hC n (a i) (b i) (y i) (z i) (s i) (r i) (ha i) (hb i)).2 le_rfl)

/-- Both derivative labels are retained separately; no subsequence is taken. -/
theorem scalar_PQQ_orthogonality {ι : Type*} {l : Filter ι}
    {u h v k : ℝ → Space → ℂ} (A : ScalarCompactApproximation u h)
    (B : ScalarCompactApproximation v k)
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => localProductNorm 5 (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (1/2) v)) l (𝓝 0) ∧
    Tendsto (fun i => localProductNorm (ENNReal.ofReal (15/8 : ℝ))
      (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (3/2) k)) l (𝓝 0) ∧
    Tendsto (fun i => localProductNorm (ENNReal.ofReal (15/8 : ℝ))
      (seedFrame (b i) (z i) (r i) (1/2) v)
      (seedFrame (a i) (y i) (s i) (3/2) h)) l (𝓝 0) := by
  have h1 := scalar_pair_PQ_orthogonality A B ha hb horth
  have horth' : Tendsto (fun i => b i/a i+a i/b i+‖z i-y i‖^2/(b i*a i)+
      |b i^2*r i-a i^2*s i|/(b i*a i)) l atTop := by
    convert horth using 1
    funext i
    rw [norm_sub_rev (z i) (y i),abs_sub_comm (b i^2*r i) (a i^2*s i)]
    ring
  exact ⟨h1.1,h1.2,(scalar_pair_PQ_orthogonality B A hb ha horth').2⟩

#print axioms scalar_pair_PQ_orthogonality
#print axioms scalar_PQQ_orthogonality
end HartreeF.LocalProfileProducts
