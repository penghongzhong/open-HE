import FCompactMollifierMixed
import FActualProfileCutoff

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation CutoffApproximation SobolevStretch

/-- The selected joint value representative retains strong measurability after cutoff. -/
theorem spacetimeCutoff_joint_stronglyMeasurable (n : ℕ) {u : ℝ → Space → ℂ}
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => spacetimeCutoff n u z.1 z.2) :=
  ((timeCutoff_smooth n).continuous.comp continuous_fst).stronglyMeasurable.smul
    (((cutoff_smooth n).continuous.comp continuous_snd).stronglyMeasurable.smul hu)

theorem packedGradient_joint_stronglyMeasurable {U V : ℝ → Space → Space}
    (hU : StronglyMeasurable (fun z : ℝ × Space => U z.1 z.2))
    (hV : StronglyMeasurable (fun z : ℝ × Space => V z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => complexGradient (U z.1) (V z.1) z.2) := by
  simp_rw [packedGradient_formula]
  exact (realEmbed_continuous.comp_stronglyMeasurable hU).add
    ((realEmbed_continuous.comp_stronglyMeasurable hV).const_smul Complex.I)

/-- The literal cutoff-gradient product retains strong joint measurability. -/
theorem spacetimeCutoffGradient_joint_stronglyMeasurable (n : ℕ)
    {u : ℝ → Space → ℂ} {G : ℝ → Space → CGradient}
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hG : StronglyMeasurable (fun z : ℝ × Space => G z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => spacetimeCutoffGradient n u G z.1 z.2) := by
  exact ((timeCutoff_smooth n).continuous.comp continuous_fst).stronglyMeasurable.smul
    ((((cutoff_smooth n).continuous.comp continuous_snd).stronglyMeasurable.smul hG).add
      (hu.smul (realEmbed_continuous.comp
        ((WeakCutoffLp.cutoff_gradient_continuous (cutoff_smooth n)).comp continuous_snd)).stronglyMeasurable))

local instance : Fact (1 ≤ (10 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ENNReal.ofReal (10/9 : ℝ)) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (ENNReal.ofReal (10/9 : ℝ)) 10 := by
  have h : Real.HolderTriple (10/9) 10 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal
local instance : Fact (1 ≤ ENNReal.ofReal (30/17 : ℝ)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ ENNReal.ofReal (30/13 : ℝ)) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (ENNReal.ofReal (30/17 : ℝ))
    (ENNReal.ofReal (30/13 : ℝ)) := by
  have h : Real.HolderTriple (30/17) (30/13) 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_one] using h.ennrealOfReal

/-- At each fixed cutoff scale, genuine spatial smoothing converges in the critical S norm. -/
theorem cutoff_mollify_S_tendsto (n : ℕ) {φ : ℕ → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : ℝ → Space → ℂ) (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hS : mixedNorm volume volume 10 10 u ≠ ∞) :
    Tendsto (fun m => mixedNorm volume volume 10 10
      (fun t x => spatialMollify (φ m) (spacetimeCutoff n u t) x - spacetimeCutoff n u t x))
      atTop (𝓝 0) :=
  spatialMollify_compact_mixed_sub_tendsto (r := ENNReal.ofReal (10/9 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) hφ _
    (spacetimeCutoff_joint_stronglyMeasurable n hu) (spacetimeCutoff_compact n u)
    (ne_top_of_le_ne_top hS (spacetime_cutoff_S_bound n u hu.aestronglyMeasurable))

/-- At each fixed cutoff scale, the actual cutoff gradient converges in the critical W norm. -/
theorem cutoff_mollify_W_tendsto (n : ℕ) {φ : ℕ → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : ℝ → Space → ℂ) (G : ℝ → Space → CGradient)
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hG : StronglyMeasurable (fun z : ℝ × Space => G z.1 z.2))
    (hS : mixedNorm volume volume 10 10 u ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) G ≠ ∞) :
    Tendsto (fun m => mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t x => spatialMollify (φ m) (spacetimeCutoffGradient n u G t) x -
        spacetimeCutoffGradient n u G t x)) atTop (𝓝 0) := by
  apply spatialMollify_compact_mixed_sub_tendsto (r := ENNReal.ofReal (30/17 : ℝ))
    (by norm_num) (by norm_num) ENNReal.ofReal_ne_top hφ _
    (spacetimeCutoffGradient_joint_stronglyMeasurable n hu hG) (spacetimeCutoffGradient_compact n u G)
  exact ne_top_of_le_ne_top (by finiteness)
    (spacetime_cutoff_W_bound n u G hu.aestronglyMeasurable hG.aestronglyMeasurable)

/-- The weak-gradient producer supplies L2 slices; smoothing contracts their full uniform energy norm. -/
theorem cutoff_mollify_energy_le (n : ℕ) (φ : ContDiffBump (0 : Space))
    (u : ℝ → Space → ℂ) (U V : ℝ → Space → Space)
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hU : StronglyMeasurable (fun z : ℝ × Space => U z.1 z.2))
    (hV : StronglyMeasurable (fun z : ℝ × Space => V z.1 z.2))
    (hd : ∀ᵐ t ∂volume, InDotH1 (u t) (U t) (V t)) :
    mixedNorm volume volume ∞ 2
      (fun t => spatialMollify φ (spacetimeCutoffGradient n u (fun s => complexGradient (U s) (V s)) t)) ≤
    mixedNorm volume volume ∞ 2 (spacetimeCutoffGradient n u (fun t => complexGradient (U t) (V t))) := by
  apply spatialMollify_compact_mixed_le (r := 2) (by norm_num) φ _
    (spacetimeCutoffGradient_joint_stronglyMeasurable n hu (packedGradient_joint_stronglyMeasurable hU hV))
    (spacetimeCutoffGradient_compact n u _)
  filter_upwards [spacetime_cutoff_domain n hd] with t ht
  have he : spacetimeCutoffGradient n u (fun s => complexGradient (U s) (V s)) t =
      complexGradient (localizedRealGradient n u U t) (localizedImagGradient n u V t) :=
    funext (spacetimeCutoffGradient_is_packed n u U V t)
  rw [he]
  exact packedGradient_memLp ht.real_gradient_L2 ht.imag_gradient_L2

#print axioms cutoff_mollify_S_tendsto
#print axioms cutoff_mollify_W_tendsto
#print axioms cutoff_mollify_energy_le
end HartreeF.ProfileSpatialSmoothing
