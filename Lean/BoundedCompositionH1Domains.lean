import HartreeLocalFactorWeakEndpoint

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.WeakHartreeProduct
open SobolevStretch StationarySelfTest ModulusGradient WeakHartreeChain

theorem bounded_complex_composition_domains {F : ℂ → ℝ} {B : ℝ≥0}
    (hF : ContDiff ℝ 1 F) (hz : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ B)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) :
    MemLp (fun x => F (u x)) 6 volume ∧ MemLp (complexChainGradient F u U V) 2 volume := by
  have hLip : LipschitzWith B F := lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp))
    (fun z => NNReal.coe_le_coe.mp (hbound z))
  have hc := hF.continuous_fderiv (by simp)
  have hcoef (e : ℂ) (he : ‖e‖ = 1) : MemLp (fun x => fderiv ℝ F (u x) e) ∞ volume := by
    apply memLp_top_of_bound ((hc.clm_apply continuous_const).comp_aestronglyMeasurable hu.function_L6.aestronglyMeasurable) B
    filter_upwards [] with x
    exact ((fderiv ℝ F (u x)).le_opNorm e).trans (by simpa only [he,mul_one] using hbound (u x))
  exact ⟨hLip.comp_memLp hz hu.function_L6,
    ((hcoef 1 (by simp)).smul hu.real_gradient_L2).add
      ((hcoef Complex.I (by simp)).smul hu.imag_gradient_L2)⟩

theorem retracted_localFactor_H1_domains (hDensity : OrdinaryH1Density)
    {q : ℝ} (hq : 1 < q) (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) (n : ℕ) :
    let F := retractedMap (projectedLocalFactor q L) (saturationParameter n)
    MemLp (fun x => F (u x)) 6 volume ∧
    MemLp (complexChainGradient F u U V) 2 volume ∧
    HasWeakGradient (fun x => F (u x)) (complexChainGradient F u U V) := by
  dsimp only
  have he := saturationParameter_pos n
  have hf := retractedMap_contDiff_one (projectedLocalFactor_contDiff_one hq L) he.le
  have hz : retractedMap (projectedLocalFactor q L) (saturationParameter n) 0 = 0 :=
    retractedMap_zero (by simp [projectedLocalFactor,localFactor]) _
  let B : ℝ≥0 := ⟨(3*(q+1))*(1+(saturationParameter n)⁻¹)^q, by positivity⟩
  have hd (z : ℂ) : ‖fderiv ℝ (retractedMap (projectedLocalFactor q L) (saturationParameter n)) z‖ ≤ B :=
    retractedMap_fderiv_bounded (projectedLocalFactor_contDiff_one hq L) (by linarith)
      (by linarith : 0 ≤ q+1) he (projectedLocalFactor_fderiv_bound hq L hL) z
  have hdom := bounded_complex_composition_domains hf hz hd hu
  exact ⟨hdom.1,hdom.2,hasWeakGradient_bounded_complex_comp_dotH1 hDensity hf hz hd hu⟩

#print axioms bounded_complex_composition_domains
#print axioms retracted_localFactor_H1_domains
end HartreeF.WeakHartreeProduct
