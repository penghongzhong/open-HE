import FActualMollifiedDomain
import FActualMollifierJointNorms
import FMixedApproximationTriangle

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation EnergySpace CriticalTimeSobolev CutoffApproximation SobolevStretch
attribute [local instance 101] secondCountableTopologyEither_of_left
attribute [local irreducible] energySubmodule timeCutoff cutoff spatialMollify
  mollifiedCutoffValue mollifiedCutoffRealGradient mollifiedCutoffImagGradient mollifiedCutoffPackedGradient

/-- The original EnergyState representative and its selected joint representative have the same
mixed-norm error against every actual comparison field. -/
theorem error_to_stateValue_eq_joint (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    (v : ℝ → Space → ℂ) (p q : ℝ≥0∞) :
    mixedNorm volume volume p q (fun t x => v t x - stateValueField g t x) =
      mixedNorm volume volume p q (fun t x => v t x - r.u t x) := by
  apply eLpNorm_congr_ae
  filter_upwards [r.slice_eq] with t ht
  apply eLpNorm_congr_ae
  filter_upwards [ht.1] with x hx
  rw [show r.u t x = stateValueField g t x from hx]

theorem error_to_stateGradient_eq_joint (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    (H : ℝ → Space → CGradient) (p q : ℝ≥0∞) :
    mixedNorm volume volume p q (fun t x => H t x -
      complexGradient (stateRealGradientField g t) (stateImagGradientField g t) x) =
      mixedNorm volume volume p q (fun t x => H t x - complexGradient (r.U t) (r.V t) x) := by
  apply eLpNorm_congr_ae
  filter_upwards [r.slice_eq] with t ht
  apply eLpNorm_congr_ae
  filter_upwards [ht.2.1, ht.2.2] with x hU hV
  simp only [complexGradient, stateRealGradientField, stateImagGradientField, hU, hV]

/-- Native compact approximation of an actual continuous homogeneous-energy profile.
One common spatial smoothing scale preserves the coupled weak gradient, converges in both
critical S/W norms, and preserves the cutoff's radius-independent homogeneous E bound.
No scalar L2 or variance hypothesis, density interface, or time-derivative requirement is used. -/
theorem actual_profile_compact_spatial_approximation {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : Continuous g) (hE : curveEnergy g ≠ ∞)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞) :
    ∃ m : ℕ → ℕ,
      (∀ n, Continuous (fun z : ℝ × Space => mollifiedCutoffValue n (shrinkingBump (m n)) g z.1 z.2)) ∧
      (∀ n, Continuous (fun z : ℝ × Space => mollifiedCutoffPackedGradient n (shrinkingBump (m n)) g z.1 z.2)) ∧
      (∀ n, HasCompactSupport (fun z : ℝ × Space => mollifiedCutoffValue n (shrinkingBump (m n)) g z.1 z.2)) ∧
      (∀ n, HasCompactSupport (fun z : ℝ × Space => mollifiedCutoffPackedGradient n (shrinkingBump (m n)) g z.1 z.2)) ∧
      (∀ n t, InDotH1 (mollifiedCutoffValue n (shrinkingBump (m n)) g t)
        (mollifiedCutoffRealGradient n (shrinkingBump (m n)) g t)
        (mollifiedCutoffImagGradient n (shrinkingBump (m n)) g t)) ∧
      Tendsto (fun n => mixedNorm volume volume 10 10
        (fun t x => mollifiedCutoffValue n (shrinkingBump (m n)) g t x - stateValueField g t x)) atTop (𝓝 0) ∧
      Tendsto (fun n => mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t x => mollifiedCutoffPackedGradient n (shrinkingBump (m n)) g t x -
          complexGradient (stateRealGradientField g t) (stateImagGradientField g t) x)) atTop (𝓝 0) ∧
      (∀ n, mixedNorm volume volume ∞ 2 (mollifiedCutoffPackedGradient n (shrinkingBump (m n)) g) ≤
        (1 + (cutoffGradientBound : ℝ≥0∞) * ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹))) * curveEnergy g) ∧
      (∀ n, mixedNorm volume volume ∞ 2 (mollifiedCutoffPackedGradient n (shrinkingBump (m n)) g) ≠ ∞) := by
  let r := energyJointFields volume g hg.aestronglyMeasurable
  let G : ℝ → Space → CGradient := fun t => complexGradient (r.U t) (r.V t)
  have hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume) :=
    packedGradient_joint_measurable r.joint_U.aestronglyMeasurable r.joint_V.aestronglyMeasurable
  have hc := actual_profile_compact_cutoff hSob g hg.aestronglyMeasurable hE hS hW
  obtain ⟨m, hmS, hmW⟩ := exists_common_smoothing_scale
    (fun n => actual_mollifiedCutoff_S_joint_tendsto g r hS n shrinkingBump_rOut_tendsto)
    (fun n => actual_mollifiedCutoff_W_joint_tendsto g r hS hW n shrinkingBump_rOut_tendsto)
  refine ⟨m, (fun n => mollifiedCutoffValue_continuous n _ g hg),
    (fun n => mollifiedCutoffPackedGradient_continuous n _ g hg),
    (fun n => mollifiedCutoffValue_compact n _ g),
    (fun n => mollifiedCutoffPackedGradient_compact n _ g),
    (fun n => actual_mollifiedCutoff_inDotH1 n _ g), ?_, ?_,
    (fun n => actual_mollifiedCutoff_energy_le hSob g hg.aestronglyMeasurable n _),
    (fun n => actual_mollifiedCutoff_energy_ne_top hSob g hg.aestronglyMeasurable hE n _)⟩
  · have ht := tendsto_zero_of_le_precision_add hc.2.2.1 (a := fun n => mixedNorm volume volume 10 10
        (fun t x => mollifiedCutoffValue n (shrinkingBump (m n)) g t x - r.u t x)) (fun n =>
      (mixed_sub_triangle (p := 10) (q := 10) (by norm_num) (by norm_num) (by norm_num)
        (mollifiedCutoffValue n (shrinkingBump (m n)) g) (spacetimeCutoff n r.u) r.u
        (mollifiedCutoffValue_continuous n _ g hg).aestronglyMeasurable
        (spacetimeCutoff_joint_measurable n r.joint_u.aestronglyMeasurable)
        r.joint_u.aestronglyMeasurable).trans (add_le_add (hmS n) le_rfl))
    apply ht.congr'
    filter_upwards [] with n
    exact (error_to_stateValue_eq_joint g r _ 10 10).symm
  · have ht := tendsto_zero_of_le_precision_add hc.2.2.2.1 (a := fun n => mixedNorm volume volume 10
        (ENNReal.ofReal (30/13 : ℝ)) (fun t x => mollifiedCutoffPackedGradient n (shrinkingBump (m n)) g t x - G t x)) (fun n =>
      (mixed_sub_triangle (p := 10) (q := ENNReal.ofReal (30/13 : ℝ)) (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
        (mollifiedCutoffPackedGradient n (shrinkingBump (m n)) g) (spacetimeCutoffGradient n r.u G) G
        (mollifiedCutoffPackedGradient_continuous n _ g hg).aestronglyMeasurable
        (spacetimeCutoffGradient_joint_stronglyMeasurable n r.joint_u
          (packedGradient_joint_stronglyMeasurable r.joint_U r.joint_V)).aestronglyMeasurable hG).trans
        (add_le_add (hmW n) le_rfl))
    apply ht.congr'
    filter_upwards [] with n
    exact (error_to_stateGradient_eq_joint g r _ 10 (ENNReal.ofReal (30/13 : ℝ))).symm

/-- Epsilon form for consumers requiring a single coupled continuous compact approximation. -/
theorem exists_actual_profile_compact_approximation {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : Continuous g) (hE : curveEnergy g ≠ ∞)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (u : ℝ → Space → ℂ) (U V : ℝ → Space → Space),
      Continuous (fun z : ℝ × Space => u z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => complexGradient (U z.1) (V z.1) z.2) ∧
      HasCompactSupport (fun z : ℝ × Space => u z.1 z.2) ∧
      HasCompactSupport (fun z : ℝ × Space => complexGradient (U z.1) (V z.1) z.2) ∧
      (∀ t, InDotH1 (u t) (U t) (V t)) ∧
      mixedNorm volume volume 10 10 (fun t x => u t x - stateValueField g t x) < ε ∧
      mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
        (fun t x => complexGradient (U t) (V t) x -
          complexGradient (stateRealGradientField g t) (stateImagGradientField g t) x) < ε ∧
      mixedNorm volume volume ∞ 2 (fun t => complexGradient (U t) (V t)) ≤
        (1 + (cutoffGradientBound : ℝ≥0∞) * ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹))) * curveEnergy g := by
  obtain ⟨m, hcu, hcG, hku, hkG, hd, hs, hw, he, _⟩ :=
    actual_profile_compact_spatial_approximation hSob g hg hE hS hW
  obtain ⟨n, hnS, hnW⟩ := ((hs.eventually (eventually_lt_nhds hε)).and
    (hw.eventually (eventually_lt_nhds hε))).exists
  refine ⟨mollifiedCutoffValue n (shrinkingBump (m n)) g,
    mollifiedCutoffRealGradient n (shrinkingBump (m n)) g,
    mollifiedCutoffImagGradient n (shrinkingBump (m n)) g, hcu n, ?_, hku n, ?_, hd n, hnS, ?_, ?_⟩
  · simpa only [mollifiedCutoffPackedGradient] using hcG n
  · simpa only [mollifiedCutoffPackedGradient] using hkG n
  · simpa only [mollifiedCutoffPackedGradient] using hnW
  · have hfun : (fun t => complexGradient (mollifiedCutoffRealGradient n (shrinkingBump (m n)) g t)
        (mollifiedCutoffImagGradient n (shrinkingBump (m n)) g t)) =
        mollifiedCutoffPackedGradient n (shrinkingBump (m n)) g := by
      funext t x
      simp only [mollifiedCutoffPackedGradient]
    rw [hfun]
    exact he n

#print axioms actual_profile_compact_spatial_approximation
#print axioms exists_actual_profile_compact_approximation
end HartreeF.ProfileSpatialSmoothing
