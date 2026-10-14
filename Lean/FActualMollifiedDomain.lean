import FActualMollifiedFields
import FCompactMollifierMixed
import FActualMollifierTransport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation EnergySpace CriticalTimeSobolev CutoffApproximation SobolevStretch
attribute [local irreducible] energySubmodule timeCutoff cutoff

/-- Every actual EnergyState time slice has the coupled localized homogeneous Sobolev domain. -/
theorem actual_cutoff_inDotH1 (n : ℕ) (g : ℝ → EnergyState) (t : ℝ) :
    InDotH1 (spacetimeCutoff n (stateValueField g) t)
      (localizedRealGradient n (stateValueField g) (stateRealGradientField g) t)
      (localizedImagGradient n (stateValueField g) (stateImagGradientField g) t) :=
  inDotH1_real_smul (cutoff_L2_and_dotH1 (energyState_inDotH1 (g t)) n).2 (timeCutoff n t)

/-- Spatial smoothing preserves the actual homogeneous weak-gradient coupling at every time. -/
theorem actual_mollifiedCutoff_inDotH1 (n : ℕ) (φ : ContDiffBump (0 : Space))
    (g : ℝ → EnergyState) (t : ℝ) :
    InDotH1 (mollifiedCutoffValue n φ g t) (mollifiedCutoffRealGradient n φ g t)
      (mollifiedCutoffImagGradient n φ g t) := by
  have hd := actual_cutoff_inDotH1 n g t
  have hcU : HasCompactSupport (fun z : ℝ × Space =>
      localizedRealGradient n (stateValueField g) (stateRealGradientField g) z.1 z.2) :=
    localizedGradient_compact n (fun t x => (stateValueField g t x).re) (stateRealGradientField g)
  have hcV : HasCompactSupport (fun z : ℝ × Space =>
      localizedImagGradient n (stateValueField g) (stateImagGradientField g) z.1 z.2) :=
    localizedGradient_compact n (fun t x => (stateValueField g t x).im) (stateImagGradientField g)
  have hu : Integrable (spacetimeCutoff n (stateValueField g) t) volume :=
    integrable_of_memLp_compact (p := 6) (by norm_num) hd.function_L6
      (compact_spacetime_slice (f := spacetimeCutoff n (stateValueField g))
        (spacetimeCutoff_compact n (stateValueField g)) t)
  have hU : Integrable (localizedRealGradient n (stateValueField g) (stateRealGradientField g) t) volume :=
    integrable_of_memLp_compact (p := 2) (by norm_num) hd.real_gradient_L2
      (compact_spacetime_slice (f := localizedRealGradient n (stateValueField g) (stateRealGradientField g)) hcU t)
  have hV : Integrable (localizedImagGradient n (stateValueField g) (stateImagGradientField g) t) volume :=
    integrable_of_memLp_compact (p := 2) (by norm_num) hd.imag_gradient_L2
      (compact_spacetime_slice (f := localizedImagGradient n (stateValueField g) (stateImagGradientField g)) hcV t)
  exact inDotH1_spatialMollify φ hd hu hU hV

attribute [local irreducible] mollifiedCutoffValue mollifiedCutoffRealGradient
  mollifiedCutoffImagGradient mollifiedCutoffPackedGradient spatialMollify

/-- The coupled packed gradient has compact spacetime support. -/
theorem mollifiedCutoffPackedGradient_compact (n : ℕ) (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) :
    HasCompactSupport (fun z : ℝ × Space => mollifiedCutoffPackedGradient n φ g z.1 z.2) := by
  simp only [mollifiedCutoffPackedGradient_eq_spatialMollify]
  exact spatialMollify_joint_compact φ
    (spacetimeCutoffGradient n (stateValueField g)
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)))
    (spacetimeCutoffGradient_compact n (stateValueField g)
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)))

/-- All geometry and differential coupling are produced for the actual mollified EnergyState profile. -/
theorem actual_mollifiedCutoff_geometry (n : ℕ) (φ : ContDiffBump (0 : Space))
    (g : ℝ → EnergyState) (hg : Continuous g) :
    Continuous (fun z : ℝ × Space => mollifiedCutoffValue n φ g z.1 z.2) ∧
    Continuous (fun z : ℝ × Space => mollifiedCutoffPackedGradient n φ g z.1 z.2) ∧
    HasCompactSupport (fun z : ℝ × Space => mollifiedCutoffValue n φ g z.1 z.2) ∧
    HasCompactSupport (fun z : ℝ × Space => mollifiedCutoffPackedGradient n φ g z.1 z.2) ∧
    (∀ t, InDotH1 (mollifiedCutoffValue n φ g t) (mollifiedCutoffRealGradient n φ g t)
      (mollifiedCutoffImagGradient n φ g t)) :=
  ⟨mollifiedCutoffValue_continuous n φ g hg, mollifiedCutoffPackedGradient_continuous n φ g hg,
    mollifiedCutoffValue_compact n φ g, mollifiedCutoffPackedGradient_compact n φ g,
    actual_mollifiedCutoff_inDotH1 n φ g⟩

#print axioms actual_mollifiedCutoff_geometry
end HartreeF.ProfileSpatialSmoothing
