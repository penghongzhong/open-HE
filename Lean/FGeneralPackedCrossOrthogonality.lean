import FGeneralScalarCrossOrthogonality
import FGeneralPackedFrame

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing CompactCross CrossContinuity ForcingDomain

/-- Four separate actual Euclidean-vector N limits, from coordinate cross decay and
the finite-dimensional norm bound. The original arbitrary filter remains unchanged. -/
theorem packed_four_cross_orthogonality {ι : Type*} {l : Filter ι}
    {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u v : ℝ → Space → ℂ} {G H : ℝ → Space → CGradient}
    (hG : StronglyMeasurable (fun z : ℝ × Space => G z.1 z.2))
    (hH : StronglyMeasurable (fun z : ℝ × Space => H z.1 z.2))
    (A : ∀ j : Fin 3, ScalarCompactApproximation u (gradientCoordinate j G))
    (B : ∀ j : Fin 3, ScalarCompactApproximation v (gradientCoordinate j H))
    {a b s r : ι → ℝ} {y z : ι → Space}
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horth : Tendsto (fun i => a i/b i+b i/a i+‖y i-z i‖^2/(a i*b i)+
      |a i^2*s i-b i^2*r i|/(a i*b i)) l atTop) :
    Tendsto (fun i => vectorForcingNorm (packedInnerCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (gradientFrame (a i) (y i) (s i) G) (seedFrame (b i) (z i) (r i) (1/2) v))) l (𝓝 0) ∧
    Tendsto (fun i => vectorForcingNorm (packedOuterCross α c (seedFrame (a i) (y i) (s i) (1/2) u)
      (seedFrame (b i) (z i) (r i) (1/2) v) (gradientFrame (b i) (z i) (r i) H))) l (𝓝 0) ∧
    Tendsto (fun i => vectorForcingNorm (packedInnerCross α c (seedFrame (b i) (z i) (r i) (1/2) v)
      (gradientFrame (b i) (z i) (r i) H) (seedFrame (a i) (y i) (s i) (1/2) u))) l (𝓝 0) ∧
    Tendsto (fun i => vectorForcingNorm (packedOuterCross α c (seedFrame (b i) (z i) (r i) (1/2) v)
      (seedFrame (a i) (y i) (s i) (1/2) u) (gradientFrame (a i) (y i) (s i) G))) l (𝓝 0) := by
  have hc (j : Fin 3) := scalar_four_cross_orthogonality hHLS (A j) (B j) ha hb horth
  have hu (i : ι) := (seedFrame_joint_stronglyMeasurable (a i) (y i) (s i) (1/2) u (A 0).profile.value_joint).aestronglyMeasurable (μ := volume.prod volume)
  have hv (i : ι) := (seedFrame_joint_stronglyMeasurable (b i) (z i) (r i) (1/2) v (B 0).profile.value_joint).aestronglyMeasurable (μ := volume.prod volume)
  have hg (i : ι) := (gradientFrame_joint_stronglyMeasurable (a i) (y i) (s i) G hG).aestronglyMeasurable (μ := volume.prod volume)
  have hh (i : ι) := (gradientFrame_joint_stronglyMeasurable (b i) (z i) (r i) H hH).aestronglyMeasurable (μ := volume.prod volume)
  refine ⟨?_,?_,?_,?_⟩
  · apply packedInnerCross_tendsto_zero α c _ _ _ hu hg hv
    intro j
    simpa only [gradientFrame_coordinate] using (hc j).1
  · apply packedOuterCross_tendsto_zero α c _ _ _ hu hv hh
    intro j
    simpa only [gradientFrame_coordinate] using (hc j).2.1
  · apply packedInnerCross_tendsto_zero α c _ _ _ hv hh hu
    intro j
    simpa only [gradientFrame_coordinate] using (hc j).2.2.1
  · apply packedOuterCross_tendsto_zero α c _ _ _ hv hu hg
    intro j
    simpa only [gradientFrame_coordinate] using (hc j).2.2.2

#print axioms packed_four_cross_orthogonality
end HartreeF.GeneralProfileCross
