import FSpatialMollifierLp
import FCutoffH1Operators

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing

/-- The actual translated normalized kernel as a spatial L2 element. -/
def kernelLpTwo (φ : ContDiffBump (0 : Space)) (x : Space) :
    Lp ℝ 2 (volume : Measure Space) :=
  lpShift (-x) (((φ.continuous_normed (μ := (volume : Measure Space))).memLp_of_hasCompactSupport (p := 2) (μ := (volume : Measure Space)) (φ.hasCompactSupport_normed (μ := (volume : Measure Space)))).toLp _)

theorem kernelLpTwo_continuous (φ : ContDiffBump (0 : Space)) : Continuous (kernelLpTwo φ) :=
  (lpShift_continuous (p := 2) (by norm_num) _).comp continuous_neg

theorem kernelLpTwo_ae (φ : ContDiffBump (0 : Space)) (x : Space) :
    (kernelLpTwo φ x : Space → ℝ) =ᵐ[volume] fun y => φ.normed volume (x - y) := by
  let hφ := (φ.continuous_normed (μ := (volume : Measure Space))).memLp_of_hasCompactSupport (p := 2) (μ := (volume : Measure Space)) (φ.hasCompactSupport_normed (μ := (volume : Measure Space)))
  filter_upwards [lpShift_coe_ae (-x) (hφ.toLp _),
    hφ.coeFn_toLp.comp_tendsto (measurePreserving_add_right volume (-x)).quasiMeasurePreserving.tendsto_ae] with y hy hyφ
  dsimp only [Function.comp_apply] at hyφ
  rw [show kernelLpTwo φ x y = hφ.toLp _ (y + -x) from hy, hyφ]
  have hn := φ.normed_neg (μ := (volume : Measure Space)) (x - y)
  rw [neg_sub] at hn
  simpa only [sub_eq_add_neg] using hn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Point evaluation of the literal mollification is an actual L2 dual pairing. -/
theorem spatialMollify_eq_pairing (φ : ContDiffBump (0 : Space))
    (f : Lp E 2 (volume : Measure Space)) (x : Space) :
    spatialMollify φ f x =
      (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing volume 2 2 (kernelLpTwo φ x) f := by
  rw [ContinuousLinearMap.lpPairing_eq_integral, spatialMollify, convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [kernelLpTwo_ae φ x] with y hy
  simp only [ContinuousLinearMap.lsmul_apply, hy]

/-- A continuous L2-valued path becomes jointly continuous after fixed spatial smoothing. -/
theorem spatialMollify_joint_continuous {T : Type*} [TopologicalSpace T]
    (φ : ContDiffBump (0 : Space)) (g : T → Lp E 2 (volume : Measure Space)) (hg : Continuous g) :
    Continuous (fun z : T × Space => spatialMollify φ (g z.1) z.2) := by
  simp_rw [spatialMollify_eq_pairing]
  exact ((ContinuousLinearMap.lsmul ℝ ℝ).lpPairing volume 2 2).continuous₂.comp₂
    ((kernelLpTwo_continuous φ).comp continuous_snd) (hg.comp continuous_fst)

#print axioms spatialMollify_joint_continuous
end HartreeF.ProfileSpatialSmoothing
