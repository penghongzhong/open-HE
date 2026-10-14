import HartreePowerCalculus
import HartreeForcingDomain
import WeakLpGradientClosure

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeChain

def densityGradient (p : ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  fun x => densityDerivative p (u x) 1 • U x+densityDerivative p (u x) Complex.I • V x

theorem densityGradient_formula (p : ℝ) (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    densityGradient p u U V x =
      (p*‖u x‖^(p-2)) • ((u x).re • U x+(u x).im • V x) := by
  simp only [densityGradient, densityDerivative_apply, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add, smul_add, smul_smul]

theorem densityDerivative_component_bound {p : ℝ} (hp : 1 < p) (z e : ℂ) (he : ‖e‖ = 1) :
    ‖densityDerivative p z e‖ ≤ p*‖z‖^(p-1) := by
  simpa only [densityDerivative_norm hp,he,mul_one] using (densityDerivative p z).le_opNorm e

theorem density_Lp {p s : ℝ} (hp : 0 < p) {u : Space → ℂ}
    (hu : MemLp u (ENNReal.ofReal s) volume) :
    MemLp (fun x => density p (u x)) (ENNReal.ofReal (s/p)) volume :=
  ForcingDomain.norm_power_memLp hp hu

theorem densityGradient_memLp {p : ℝ} (hp : 1 < p)
    {u : Space → ℂ} {U V : Space → Space}
    (hu : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (densityGradient p u U V) (ENNReal.ofReal (30/(3*p+10))) volume := by
  have hpow : MemLp (fun x => ‖u x‖^(p-1)) (ENNReal.ofReal (10/(p-1))) volume :=
    ForcingDomain.norm_power_memLp (by linarith : 0 < p-1) (by simpa using hu)
  have hcont := densityDerivative_continuous hp
  have hcoeff (e : ℂ) (he : ‖e‖ = 1) :
      MemLp (fun x => densityDerivative p (u x) e) (ENNReal.ofReal (10/(p-1))) volume := by
    apply (hpow.const_mul p).of_le
      ((hcont.clm_apply continuous_const).comp_aestronglyMeasurable hu.aestronglyMeasurable)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by linarith : 0 ≤ p) (Real.rpow_nonneg (norm_nonneg _) _))] using
      densityDerivative_component_bound hp (u x) e he
  have hh : Real.HolderTriple (10/(p-1)) (30/13) (30/(3*p+10)) := by
    constructor
    · field_simp
      ring
    · positivity
    · norm_num
  let := hh.ennrealOfReal
  exact ((hcoeff 1 (by simp)).smul hU).add ((hcoeff Complex.I (by simp)).smul hV)

#print axioms densityGradient_formula
#print axioms densityDerivative_component_bound
#print axioms density_Lp
#print axioms densityGradient_memLp
end HartreeF.WeakHartreeChain
