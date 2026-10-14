import FGeneralFrameCrossContinuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing CompactCross CrossContinuity ForcingDomain

/-- Two separate pure-cross limits for literal scalar profiles with constructed compact
approximations. The approximation index is independent of the original filter index. -/
theorem scalar_pair_cross_orthogonality {ι : Type*} {l : Filter ι}
    {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u h v k : ℝ → Space → ℂ} (A : ScalarCompactApproximation u h)
    (B : ScalarCompactApproximation v k)
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => forcingNorm (innerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (a i) (y i) (s i) (3/2) h) (seedFrame (b i) (z i) (r i) (1/2) v))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (outerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (1/2) v) (seedFrame (b i) (z i) (r i) (3/2) k))) l (𝓝 0) := by
  obtain ⟨C,hC⟩ := bounded_pair_frame_error hHLS A B
  let e : ℕ → ℝ≥0∞ := fun n => (C : ℝ≥0∞) *
    boundedModulus α (2*(A.bound+B.bound)) (smoothingPrecision n+smoothingPrecision n)
  have he : Tendsto e atTop (𝓝 0) := by
    have hd := smoothingPrecision_tendsto.add smoothingPrecision_tendsto
    simp only [zero_add] at hd
    have hm := (boundedModulus_tendsto_zero hHLS.order_pos hHLS.order_lt_three (2*(A.bound+B.bound))).comp hd
    simpa only [e, Function.comp_apply, mul_zero] using ENNReal.Tendsto.const_mul hm (a := (C : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
  have hc (n : ℕ) := compact_four_pure_cross_orthogonality hHLS
    (A.value_continuous n) (A.gradient_continuous n) (B.value_continuous n) (B.gradient_continuous n)
    (A.value_compact n) (A.gradient_compact n) (B.value_compact n) (B.gradient_compact n) ha hb horth
  constructor
  · apply tendsto_zero_of_uniform_approximation he (fun n => (hc n).1)
    intro n i
    have h1 := A.profile.frame (ha i) (y i) (s i)
    have h2 := B.profile.frame (hb i) (z i) (r i)
    have h3 := (A.approximate_profile n).frame (ha i) (y i) (s i)
    have h4 := (B.approximate_profile n).frame (hb i) (z i) (r i)
    exact (forcingNorm_le_difference_add _ _
      (inner_joint_measurable α c h1.value_joint.aestronglyMeasurable h1.gradient_joint.aestronglyMeasurable h2.value_joint.aestronglyMeasurable)
      (inner_joint_measurable α c h3.value_joint.aestronglyMeasurable h3.gradient_joint.aestronglyMeasurable h4.value_joint.aestronglyMeasurable)).trans
      (add_le_add (hC n (a i) (b i) (y i) (z i) (s i) (r i) (ha i) (hb i)).1 le_rfl)
  · apply tendsto_zero_of_uniform_approximation he (fun n => (hc n).2.1)
    intro n i
    have h1 := A.profile.frame (ha i) (y i) (s i)
    have h2 := B.profile.frame (hb i) (z i) (r i)
    have h3 := (A.approximate_profile n).frame (ha i) (y i) (s i)
    have h4 := (B.approximate_profile n).frame (hb i) (z i) (r i)
    exact (forcingNorm_le_difference_add _ _
      (outer_joint_measurable α c h1.value_joint.aestronglyMeasurable h2.value_joint.aestronglyMeasurable h2.gradient_joint.aestronglyMeasurable)
      (outer_joint_measurable α c h3.value_joint.aestronglyMeasurable h4.value_joint.aestronglyMeasurable h4.gradient_joint.aestronglyMeasurable)).trans
      (add_le_add (hC n (a i) (b i) (y i) (z i) (s i) (r i) (ha i) (hb i)).2 le_rfl)

/-- All four separate forcing norms converge on the original whole filter. -/
theorem scalar_four_cross_orthogonality {ι : Type*} {l : Filter ι}
    {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u h v k : ℝ → Space → ℂ} (A : ScalarCompactApproximation u h)
    (B : ScalarCompactApproximation v k)
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => forcingNorm (innerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (a i) (y i) (s i) (3/2) h) (seedFrame (b i) (z i) (r i) (1/2) v))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (outerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (1/2) v) (seedFrame (b i) (z i) (r i) (3/2) k))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (innerCross α c (seedFrame (b i) (z i) (r i) (1/2) v)
      (seedFrame (b i) (z i) (r i) (3/2) k) (seedFrame (a i) (y i) (s i) (1/2) u))) l (𝓝 0) ∧
    Tendsto (fun i => forcingNorm (outerCross α c (seedFrame (b i) (z i) (r i) (1/2) v)
      (seedFrame (a i) (y i) (s i) (1/2) u) (seedFrame (a i) (y i) (s i) (3/2) h))) l (𝓝 0) := by
  have h1 := scalar_pair_cross_orthogonality hHLS A B ha hb horth
  have horth' : Tendsto (fun i => b i/a i+a i/b i+‖z i-y i‖^2/(b i*a i)+
      |b i^2*r i-a i^2*s i|/(b i*a i)) l atTop := by
    convert horth using 1
    funext i
    rw [norm_sub_rev (z i) (y i),abs_sub_comm (b i^2*r i) (a i^2*s i)]
    ring
  have h2 := scalar_pair_cross_orthogonality hHLS B A hb ha horth'
  exact ⟨h1.1,h1.2,h2.1,h2.2⟩

#print axioms scalar_pair_cross_orthogonality
#print axioms scalar_four_cross_orthogonality
end HartreeF.GeneralProfileCross
