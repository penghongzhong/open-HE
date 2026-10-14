import FSpatialWeakCoupling
import FProfileEnergyBridge

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open SobolevStretch ProfileApproximation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

/-- Every continuous real-linear observable commutes with literal spatial mollification. -/
theorem spatialMollify_clm (φ : ContDiffBump (0 : Space)) (L : E →L[ℝ] F)
    {f : Space → E} (hf : LocallyIntegrable f volume) :
    spatialMollify φ (fun x => L (f x)) = fun x => L (spatialMollify φ f x) := by
  funext x
  have hi := ((φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed hf x).integrable_swap
  simp only [ContinuousLinearMap.lsmul_apply] at hi
  simp only [spatialMollify, convolution_lsmul_swap]
  rw [← L.integral_comp_comm hi]
  simp only [map_smul]

/-- Scalar real and imaginary parts commute pointwise, not only almost everywhere. -/
theorem spatialMollify_re (φ : ContDiffBump (0 : Space))
    {u : Space → ℂ} (hu : LocallyIntegrable u volume) :
    spatialMollify φ (fun x => (u x).re) = fun x => (spatialMollify φ u x).re :=
  spatialMollify_clm φ Complex.reCLM hu

theorem spatialMollify_im (φ : ContDiffBump (0 : Space))
    {u : Space → ℂ} (hu : LocallyIntegrable u volume) :
    spatialMollify φ (fun x => (u x).im) = fun x => (spatialMollify φ u x).im :=
  spatialMollify_clm φ Complex.imCLM hu

/-- The actual finite-dimensional real-to-complex gradient embedding, as a CLM. -/
def realEmbedCLM : Space →L[ℝ] CGradient where
  toFun := realEmbed
  map_add' := by intro a b; ext j; simp [realEmbed]
  map_smul' := by intro a b; ext j; simp [realEmbed, Complex.real_smul]
  cont := realEmbed_continuous

/-- Packing the two real mollified gradients equals mollifying the actual packed complex field. -/
theorem spatialMollify_complexGradient (φ : ContDiffBump (0 : Space))
    {U V : Space → Space} (hU : LocallyIntegrable U volume)
    (hV : LocallyIntegrable V volume) :
    complexGradient (spatialMollify φ U) (spatialMollify φ V) =
      spatialMollify φ (complexGradient U V) := by
  funext x
  have hiU := ((φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed hU x).integrable_swap
  have hiV := ((φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed hV x).integrable_swap
  simp only [ContinuousLinearMap.lsmul_apply] at hiU hiV
  rw [packedGradient_formula]
  simp only [spatialMollify, convolution_lsmul_swap]
  change realEmbedCLM (∫ y, φ.normed volume (x-y) • U y) +
    Complex.I • realEmbedCLM (∫ y, φ.normed volume (x-y) • V y) = _
  have hiVI : Integrable (fun y => Complex.I • realEmbedCLM (φ.normed volume (x-y) • V y)) volume := by
    let L : CGradient →L[ℝ] CGradient := Complex.I • ContinuousLinearMap.id ℝ CGradient
    exact L.integrable_comp (realEmbedCLM.integrable_comp hiV)
  rw [← realEmbedCLM.integral_comp_comm hiU, ← realEmbedCLM.integral_comp_comm hiV,
    ← integral_smul, ← integral_add (realEmbedCLM.integrable_comp hiU)
      hiVI]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [map_smul, map_smul]
  change φ.normed volume (x-y) • realEmbed (U y) +
    Complex.I • (φ.normed volume (x-y) • realEmbed (V y)) = _
  rw [packedGradient_formula, smul_add, smul_comm Complex.I (φ.normed volume (x-y))]

local instance : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (ENNReal.ofReal (6/5 : ℝ)) 6 := by
  have h : Real.HolderTriple (6/5) 6 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

/-- Complex homogeneous Sobolev coupling for the literal normalized convolution.
L1 assumptions serve only the established finite-exponent Lp producer. -/
theorem inDotH1_spatialMollify (φ : ContDiffBump (0 : Space))
    {u : Space → ℂ} {U V : Space → Space} (h : InDotH1 u U V)
    (hu : Integrable u volume) (hU : Integrable U volume) (hV : Integrable V volume) :
    InDotH1 (spatialMollify φ u) (spatialMollify φ U) (spatialMollify φ V) := by
  refine ⟨spatialMollify_memLp (q := ENNReal.ofReal (6/5 : ℝ)) (by norm_num) φ h.function_L6 hu,
    spatialMollify_memLp (q := 2) (by norm_num) φ h.real_gradient_L2 hU,
    spatialMollify_memLp (q := 2) (by norm_num) φ h.imag_gradient_L2 hV, ?_, ?_⟩
  · rw [← spatialMollify_re φ hu.locallyIntegrable]
    exact hasWeakGradient_spatialMollify φ h.real_weak
  · rw [← spatialMollify_im φ hu.locallyIntegrable]
    exact hasWeakGradient_spatialMollify φ h.imag_weak

#print axioms spatialMollify_clm
#print axioms spatialMollify_complexGradient
#print axioms inDotH1_spatialMollify
end HartreeF.ProfileSpatialSmoothing
