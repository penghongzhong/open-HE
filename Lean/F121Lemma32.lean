import ForcingLpMap
import FCriticalPathGradientSource
import FCriticalHartreeSourceSmallness
import FHartreeL2Time

/-! A literal terminal wrapper for Lemma 3.2 of the 121-page manuscript.
The three gradient-difference monomials are retained in `vectorDifferenceBudget`,
whose definition is exactly the manuscript's `M`, `N`, `D`, `e`, `Y`, `z`
formula.  The weak gradient is an actual iterated Bochner source. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.Paper121Lemma32
open EnergySpace ForcingDomain ForcingContinuity TimeHolder
open CriticalPathSpace CriticalJointSources CriticalSourceBounds
open SobolevStretch StationarySelfTest

local instance sourceExponent_one_le : Fact (1 ≤ ENNReal.ofReal (6 / 5 : ℝ)) :=
  ⟨by norm_num⟩
local instance sourceExponent_ne_top : Fact (ENNReal.ofReal (6 / 5 : ℝ) ≠ ∞) :=
  ⟨ENNReal.ofReal_ne_top⟩

universe uTime

/-- The two single-path estimates in (3), with the first left side represented
as the actual Euclidean complex weak gradient of the Hartree source. -/
def SinglePathEstimates
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (mu : Measure T) [SigmaFinite mu]
    (alpha c : ℝ) (Cgrad Cl2 : ℝ≥0) (z : CriticalPath mu) : Prop :=
  actualGradientSize mu alpha c z 0 ≤
      (Cgrad : ℝ≥0∞) * pathEnergySize mu z ^ (2 * alpha) *
        pathValueSize mu z ^ (4 : ℝ) * pathGradientSize mu z ∧
    mixedNorm mu volume 2 2
        (fun t => forcing alpha c ((jointFields mu z).u t)) ≤
      (Cl2 : ℝ≥0∞) * pathEnergySize mu z ^ (2 * alpha) *
        pathValueSize mu z ^ (5 : ℝ)

/-- The exact three-term estimate (4), together with a genuine Bochner
representative which is the distributional weak gradient on almost every
time slice. -/
def DifferenceGradientEstimate
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (mu : Measure T) [SigmaFinite mu]
    (alpha c : ℝ) (Cgrad : ℝ≥0) (z w : CriticalPath mu) : Prop :=
  actualGradientSize mu alpha c z w ≤
      (Cgrad : ℝ≥0∞) * vectorDifferenceBudget alpha mu
        (jointFields mu z).u (jointFields mu w).u
        (jointFields mu z).U (jointFields mu z).V
        (jointFields mu w).U (jointFields mu w).V ∧
    ∃ G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume : Measure Space)) 2 mu,
      (∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space), G t x =
        actualFullGradient alpha c ((jointFields mu z).u t)
            ((jointFields mu z).U t) ((jointFields mu z).V t) x -
          actualFullGradient alpha c ((jointFields mu w).u t)
            ((jointFields mu w).U t) ((jointFields mu w).V t) x) ∧
      (∀ᵐ t ∂mu,
        HasWeakGradient
            (fun x => (forcing alpha c ((jointFields mu z).u t) x -
              forcing alpha c ((jointFields mu w).u t) x).re)
            (fun x => gradientReal (G t x)) ∧
        HasWeakGradient
            (fun x => (forcing alpha c ((jointFields mu z).u t) x -
              forcing alpha c ((jointFields mu w).u t) x).im)
            (fun x => gradientImag (G t x)))

/-- Full Lemma 3.2.  Both numerical constants are chosen before the time
space, measure, and paths.  No target source norm, scalar mass, radiality, or
extra regularity is assumed. -/
theorem lemma32_nonlinearity_on_energy_and_critical_graphs
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) :
    (∀ v : Lp ℂ 6 (volume : Measure Space),
      ∃ L : ℝ≥0, LipschitzOnWith L (forcingLp hH) (Metric.ball v 1)) ∧
    ∃ Cgrad Cl2 : ℝ≥0,
      (∀ {T : Type uTime} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
        [BorelSpace T] (mu : Measure T) [SigmaFinite mu] (z : CriticalPath mu),
        SinglePathEstimates mu alpha c Cgrad Cl2 z) ∧
      (∀ {T : Type uTime} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
        [BorelSpace T] (mu : Measure T) [SigmaFinite mu] (z w : CriticalPath mu),
        DifferenceGradientEstimate mu alpha c Cgrad z w) := by
  refine ⟨fun v => forcingLp_locally_lipschitz hH v, ?_⟩
  obtain ⟨Cgrad, hgrad⟩ := actual_full_gradient_vector_difference_bound hH
  obtain ⟨Cl2, hl2⟩ := ForcingL2.forcing_l2_mixed_bound hH
  refine ⟨Cgrad, Cl2, ?_, ?_⟩
  · intro T _ _ _ _ mu _ z
    let r := jointFields mu z
    have hs := joint_slices mu hDensity hSob z z
    have hslice : ∀ᵐ t ∂mu, MemLp (r.u t) 6 volume ∧ MemLp (r.u t) 10 volume := by
      filter_upwards [hs] with t ht
      exact ⟨ht.1.function_L6, ht.2.2.1⟩
    have hg := hgrad (T := T) mu r.u (jointFields mu (0 : CriticalPath mu)).u
      r.U r.V (jointFields mu (0 : CriticalPath mu)).U
      (jointFields mu (0 : CriticalPath mu)).V
      (joint_slices mu hDensity hSob z 0)
      r.joint_u.aestronglyMeasurable
      (jointFields mu (0 : CriticalPath mu)).joint_u.aestronglyMeasurable
      r.joint_U.aestronglyMeasurable r.joint_V.aestronglyMeasurable
      (jointFields mu (0 : CriticalPath mu)).joint_U.aestronglyMeasurable
      (jointFields mu (0 : CriticalPath mu)).joint_V.aestronglyMeasurable
    have hg' : actualGradientSize mu alpha c z 0 ≤
        (Cgrad : ℝ≥0∞) * pathEnergySize mu z ^ (2 * alpha) *
          pathValueSize mu z ^ (4 : ℝ) * pathGradientSize mu z := by
      rw [joint_vectorBudget_single mu hDensity hSob z] at hg
      simpa only [actualGradientSize, r, mul_assoc] using hg
    have hl2' := hl2 (T := T) mu r.u r.joint_u.aestronglyMeasurable hslice
    refine ⟨hg', ?_⟩
    simpa only [SinglePathEstimates, pathEnergySize, pathValueSize, r, mul_assoc] using hl2'
  · intro T _ _ _ _ mu _ z w
    let rz := jointFields mu z
    let rw := jointFields mu w
    refine ⟨?_, ?_⟩
    · exact hgrad (T := T) mu rz.u rw.u rz.U rz.V rw.U rw.V
        (joint_slices mu hDensity hSob z w)
        rz.joint_u.aestronglyMeasurable rw.joint_u.aestronglyMeasurable
        rz.joint_U.aestronglyMeasurable rz.joint_V.aestronglyMeasurable
        rw.joint_U.aestronglyMeasurable rw.joint_V.aestronglyMeasurable
    · exact exists_joint_actualGradient_source_withWeak mu hDensity hSob hH z w

end HartreeF.Paper121Lemma32
