import FSpatialMollifierContinuity
import FSpatialMollifierSupport
import FActualProfileCutoff

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation EnergySpace CriticalTimeSobolev CutoffApproximation SobolevStretch
attribute [local irreducible] energySubmodule timeCutoff cutoff

abbrev stateValueField (g : ℝ → EnergyState) (t : ℝ) : Space → ℂ := energyValue (g t)
abbrev stateRealGradientField (g : ℝ → EnergyState) (t : ℝ) : Space → Space :=
  energyProjectedGradient Complex.reCLM (g t)
abbrev stateImagGradientField (g : ℝ → EnergyState) (t : ℝ) : Space → Space :=
  energyProjectedGradient Complex.imCLM (g t)

def mollifiedCutoffValue (n : ℕ) (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) (t : ℝ) : Space → ℂ :=
  spatialMollify φ (spacetimeCutoff n (stateValueField g) t)
def mollifiedCutoffRealGradient (n : ℕ) (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) (t : ℝ) : Space → Space :=
  spatialMollify φ (localizedRealGradient n (stateValueField g) (stateRealGradientField g) t)
def mollifiedCutoffImagGradient (n : ℕ) (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) (t : ℝ) : Space → Space :=
  spatialMollify φ (localizedImagGradient n (stateValueField g) (stateImagGradientField g) t)
def mollifiedCutoffPackedGradient (n : ℕ) (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) (t : ℝ) : Space → CGradient :=
  complexGradient (mollifiedCutoffRealGradient n φ g t) (mollifiedCutoffImagGradient n φ g t)

theorem time_cutoffValue_ae (n : ℕ) (g : ℝ → EnergyState) (t : ℝ) :
    ((timeCutoff n t • LocalRellich.cutoffValue n (g t) : Lp ℂ 2 (volume : Measure Space)) : Space → ℂ) =ᵐ[volume]
      spacetimeCutoff n (stateValueField g) t := by
  filter_upwards [Lp.coeFn_smul (timeCutoff n t) (LocalRellich.cutoffValue n (g t)),
    LocalRellich.cutoffValue_ae n (g t)] with x hx hy
  rw [hx]
  change timeCutoff n t • LocalRellich.cutoffValue n (g t) x = _
  rw [hy]
  rfl

theorem time_cutoffGradient_ae (L : ℂ →L[ℝ] ℝ) (n : ℕ) (g : ℝ → EnergyState) (t : ℝ) :
    ((timeCutoff n t • LocalRellich.cutoffGradient L n (g t) : Lp Space 2 (volume : Measure Space)) : Space → Space) =ᵐ[volume]
      (fun x => timeCutoff n t • (cutoff n x • energyProjectedGradient L (g t) x +
        L (energyValue (g t) x) • gradient (cutoff n) x)) := by
  filter_upwards [Lp.coeFn_smul (timeCutoff n t) (LocalRellich.cutoffGradient L n (g t)),
    LocalRellich.cutoffGradient_ae L n (g t)] with x hx hy
  rw [hx]
  change timeCutoff n t • LocalRellich.cutoffGradient L n (g t) x = _
  rw [hy]

/-- Actual continuous homogeneous EnergyState curves yield jointly continuous mollified values. -/
theorem mollifiedCutoffValue_continuous (n : ℕ) (φ : ContDiffBump (0 : Space))
    (g : ℝ → EnergyState) (hg : Continuous g) :
    Continuous (fun z : ℝ × Space => mollifiedCutoffValue n φ g z.1 z.2) := by
  have h := spatialMollify_joint_continuous φ (fun t => timeCutoff n t • LocalRellich.cutoffValue n (g t))
    ((timeCutoff_smooth n).continuous.smul ((LocalRellich.cutoffValue n).continuous.comp hg))
  convert h using 1
  funext z
  exact congrFun (spatialMollify_congr φ (time_cutoffValue_ae n g z.1)) z.2 |>.symm

theorem mollifiedCutoffRealGradient_continuous (n : ℕ) (φ : ContDiffBump (0 : Space))
    (g : ℝ → EnergyState) (hg : Continuous g) :
    Continuous (fun z : ℝ × Space => mollifiedCutoffRealGradient n φ g z.1 z.2) := by
  have h := spatialMollify_joint_continuous φ (fun t => timeCutoff n t • LocalRellich.cutoffGradient Complex.reCLM n (g t))
    ((timeCutoff_smooth n).continuous.smul ((LocalRellich.cutoffGradient Complex.reCLM n).continuous.comp hg))
  convert h using 1
  funext z
  exact congrFun (spatialMollify_congr φ (time_cutoffGradient_ae Complex.reCLM n g z.1)) z.2 |>.symm

theorem mollifiedCutoffImagGradient_continuous (n : ℕ) (φ : ContDiffBump (0 : Space))
    (g : ℝ → EnergyState) (hg : Continuous g) :
    Continuous (fun z : ℝ × Space => mollifiedCutoffImagGradient n φ g z.1 z.2) := by
  have h := spatialMollify_joint_continuous φ (fun t => timeCutoff n t • LocalRellich.cutoffGradient Complex.imCLM n (g t))
    ((timeCutoff_smooth n).continuous.smul ((LocalRellich.cutoffGradient Complex.imCLM n).continuous.comp hg))
  convert h using 1
  funext z
  exact congrFun (spatialMollify_congr φ (time_cutoffGradient_ae Complex.imCLM n g z.1)) z.2 |>.symm

theorem mollifiedCutoffPackedGradient_continuous (n : ℕ) (φ : ContDiffBump (0 : Space))
    (g : ℝ → EnergyState) (hg : Continuous g) :
    Continuous (fun z : ℝ × Space => mollifiedCutoffPackedGradient n φ g z.1 z.2) := by
  simp only [mollifiedCutoffPackedGradient, packedGradient_formula]
  exact (realEmbed_continuous.comp (mollifiedCutoffRealGradient_continuous n φ g hg)).add
    ((realEmbed_continuous.comp (mollifiedCutoffImagGradient_continuous n φ g hg)).const_smul Complex.I)

/-- The explicit real cutoff derivative has compact spacetime support before smoothing. -/
theorem localizedGradient_compact (n : ℕ) (u : ℝ → Space → ℝ) (U : ℝ → Space → Space) :
    HasCompactSupport (fun z : ℝ × Space => timeCutoff n z.1 •
      (cutoff n z.2 • U z.1 z.2 + u z.1 z.2 • gradient (cutoff n) z.2)) := by
  have hd := WeakCutoffLp.cutoff_gradient_hasCompactSupport (cutoff_compact n)
  apply HasCompactSupport.intro ((timeCutoff_compact n).prod ((cutoff_compact n).union hd))
  intro z hz
  by_cases ht : z.1 ∈ tsupport (timeCutoff n)
  · have hx : z.2 ∉ tsupport (cutoff n) := fun hx => hz ⟨ht, Or.inl hx⟩
    have hd : z.2 ∉ tsupport (gradient (cutoff n)) := fun hx => hz ⟨ht, Or.inr hx⟩
    simp [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hd]
  · simp [image_eq_zero_of_notMem_tsupport ht]

theorem mollifiedCutoffValue_compact (n : ℕ) (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) :
    HasCompactSupport (fun z : ℝ × Space => mollifiedCutoffValue n φ g z.1 z.2) :=
  spatialMollify_joint_compact φ _ (spacetimeCutoff_compact n _)

theorem mollifiedCutoffRealGradient_compact (n : ℕ) (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) :
    HasCompactSupport (fun z : ℝ × Space => mollifiedCutoffRealGradient n φ g z.1 z.2) :=
  spatialMollify_joint_compact φ (localizedRealGradient n (stateValueField g) (stateRealGradientField g))
    (localizedGradient_compact n (fun t x => (stateValueField g t x).re) (stateRealGradientField g))

theorem mollifiedCutoffImagGradient_compact (n : ℕ) (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) :
    HasCompactSupport (fun z : ℝ × Space => mollifiedCutoffImagGradient n φ g z.1 z.2) :=
  spatialMollify_joint_compact φ (localizedImagGradient n (stateValueField g) (stateImagGradientField g))
    (localizedGradient_compact n (fun t x => (stateValueField g t x).im) (stateImagGradientField g))

#print axioms mollifiedCutoffValue_continuous
#print axioms mollifiedCutoffRealGradient_continuous
#print axioms mollifiedCutoffValue_compact
end HartreeF.ProfileSpatialSmoothing
