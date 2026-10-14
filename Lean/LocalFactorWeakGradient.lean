import PolynomialWeakChain
import ProjectedLocalFactorCalculus

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeChain
open SobolevStretch StationarySelfTest

def projectedLocalFactorGradient (q : ℝ) (L : ℂ →L[ℝ] ℝ)
    (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  fun x => L (localFactorDerivative q (u x) 1) • U x+
    L (localFactorDerivative q (u x) Complex.I) • V x

theorem projectedLocalFactor_hasWeakGradient (hDensity : OrdinaryH1Density)
    {q : ℝ} (hq : 1 < q) (hq4 : q < 4) (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => projectedLocalFactor q L (u x))
      (projectedLocalFactorGradient q L u U V) := by
  have hh := polynomial_C1_hasWeakGradient hDensity (projectedLocalFactor_contDiff_one hq L)
    (by simp [projectedLocalFactor,localFactor]) hq hq4 (by linarith : 0 ≤ q+1) (by norm_num : (0 : ℝ)≤1)
    (projectedLocalFactor_norm_bound hq L hL) (projectedLocalFactor_fderiv_bound hq L hL) hu hu10 hU hV
  convert hh using 1
  funext x
  simp only [projectedLocalFactorGradient,complexChainGradient,projectedLocalFactor_fderiv hq,
    ContinuousLinearMap.comp_apply]

def localFactorGradientRe (q : ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  fun x => ‖u x‖^q • U x+(q*‖u x‖^(q-2)*(u x).re) • ((u x).re • U x+(u x).im • V x)

def localFactorGradientIm (q : ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  fun x => ‖u x‖^q • V x+(q*‖u x‖^(q-2)*(u x).im) • ((u x).re • U x+(u x).im • V x)

theorem projectedLocalFactorGradient_re (q : ℝ) (u : Space → ℂ) (U V : Space → Space) :
    projectedLocalFactorGradient q Complex.reCLM u U V = localFactorGradientRe q u U V := by
  funext x
  simp only [projectedLocalFactorGradient,localFactorDerivative_apply,Complex.one_re,Complex.one_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add,Complex.reCLM_apply,
    Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,localFactorGradientRe,add_smul,smul_add,smul_smul]
  module

theorem projectedLocalFactorGradient_im (q : ℝ) (u : Space → ℂ) (U V : Space → Space) :
    projectedLocalFactorGradient q Complex.imCLM u U V = localFactorGradientIm q u U V := by
  funext x
  simp only [projectedLocalFactorGradient,localFactorDerivative_apply,Complex.one_re,Complex.one_im,
    Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add,Complex.imCLM_apply,
    Complex.add_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,localFactorGradientIm,add_smul,smul_add,smul_smul]
  module

theorem localFactor_real_hasWeakGradient (hDensity : OrdinaryH1Density)
    {q : ℝ} (hq : 1 < q) (hq4 : q < 4)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => (localFactor q (u x)).re) (localFactorGradientRe q u U V) := by
  rw [← projectedLocalFactorGradient_re]
  exact projectedLocalFactor_hasWeakGradient hDensity hq hq4 Complex.reCLM reCLM_norm_le_one hu hu10 hU hV

theorem localFactor_imag_hasWeakGradient (hDensity : OrdinaryH1Density)
    {q : ℝ} (hq : 1 < q) (hq4 : q < 4)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => (localFactor q (u x)).im) (localFactorGradientIm q u U V) := by
  rw [← projectedLocalFactorGradient_im]
  exact projectedLocalFactor_hasWeakGradient hDensity hq hq4 Complex.imCLM imCLM_norm_le_one hu hu10 hU hV

#print axioms projectedLocalFactor_hasWeakGradient
#print axioms projectedLocalFactorGradient_re
#print axioms projectedLocalFactorGradient_im
#print axioms localFactor_real_hasWeakGradient
#print axioms localFactor_imag_hasWeakGradient
end HartreeF.WeakHartreeChain
