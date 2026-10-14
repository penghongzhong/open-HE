import LocalFactorWeakGradient
import HartreeDensityWeakEndpoint

/-! Actual real and imaginary weak gradients of |u|^(1+alpha) u.
All zero values and every 0<alpha<3 are included. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeChain
open SobolevStretch StationarySelfTest

theorem hartree_localFactor_weak_gradients (hDensity : OrdinaryH1Density)
    {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => (ForcingDomain.localFactor α u x).re)
      (localFactorGradientRe (1+α) u U V) ∧
    HasWeakGradient (fun x => (ForcingDomain.localFactor α u x).im)
      (localFactorGradientIm (1+α) u U V) := by
  exact ⟨localFactor_real_hasWeakGradient hDensity (by linarith) (by linarith) hu hu10 hU hV,
    localFactor_imag_hasWeakGradient hDensity (by linarith) (by linarith) hu hu10 hU hV⟩

theorem hartree_localFactor_memLp {α : ℝ} (hα : 0 < α)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) :
    MemLp (ForcingDomain.localFactor α u) (ENNReal.ofReal (6/(2+α))) volume :=
  ForcingDomain.localFactor_memLp hα (by simpa using hu.function_L6)

theorem projectedLocalFactorGradient_memLp {q : ℝ} (hq : 1 < q)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (projectedLocalFactorGradient q L u U V) (ENNReal.ofReal (30/(3*q+13))) volume := by
  have hm := complexChainGradient_memLp (projectedLocalFactor_contDiff_one hq L) (by linarith)
    (by linarith : 0 ≤ q+1) (projectedLocalFactor_fderiv_bound hq L hL) hu10 hU hV
  convert hm using 1
  funext x
  simp only [projectedLocalFactorGradient,complexChainGradient,projectedLocalFactor_fderiv hq,
    ContinuousLinearMap.comp_apply]

theorem hartree_localFactor_gradient_domains {α : ℝ} (hα : 0 < α)
    {u : Space → ℂ} {U V : Space → Space} (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (localFactorGradientRe (1+α) u U V) (ENNReal.ofReal (30/(16+3*α))) volume ∧
    MemLp (localFactorGradientIm (1+α) u U V) (ENNReal.ofReal (30/(16+3*α))) volume := by
  rw [← projectedLocalFactorGradient_re,← projectedLocalFactorGradient_im]
  have hr := projectedLocalFactorGradient_memLp (by linarith : 1 < 1+α)
    Complex.reCLM reCLM_norm_le_one hu10 hU hV
  have hi := projectedLocalFactorGradient_memLp (by linarith : 1 < 1+α)
    Complex.imCLM imCLM_norm_le_one hu10 hU hV
  have he : 3*(1+α)+13 = 16+3*α := by ring
  rw [he] at hr hi
  exact ⟨hr,hi⟩

#print axioms hartree_localFactor_weak_gradients
#print axioms hartree_localFactor_memLp
#print axioms projectedLocalFactorGradient_memLp
#print axioms hartree_localFactor_gradient_domains
end HartreeF.WeakHartreeChain
