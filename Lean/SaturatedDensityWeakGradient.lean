import SaturatedDensityCalculus
import BoundedComplexChain
import DensityGradientDomains
import DominatedLpConvergence
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.WeakHartreeChain
open SobolevStretch StationarySelfTest

def saturationParameter (n : ℕ) : ℝ := 1/((n : ℝ)+1)

theorem saturationParameter_pos (n : ℕ) : 0 < saturationParameter n := by
  unfold saturationParameter
  positivity

theorem saturationParameter_tendsto : Tendsto saturationParameter atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem saturationCoeff_continuous {p ε : ℝ} (hp : 1 < p) (hε : 0 ≤ ε) :
    Continuous (saturationCoeff p ε) := by
  exact (continuous_const.add (continuous_const.mul (density_contDiff_one hp).continuous)).pow 2 |>.inv₀
    (fun z => pow_ne_zero 2 (saturation_denominator_pos hε p z).ne')

theorem saturatedDensity_tendsto (p : ℝ) (z : ℂ) :
    Tendsto (fun n => saturatedDensity p (saturationParameter n) z) atTop (𝓝 (density p z)) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add (saturationParameter_tendsto.mul_const (density p z))
  convert! (tendsto_const_nhds (x := density p z)).div ht
    (by norm_num : (1 : ℝ)+0*density p z ≠ 0) using 1
  simp

theorem saturationCoeff_tendsto (p : ℝ) (z : ℂ) :
    Tendsto (fun n => saturationCoeff p (saturationParameter n) z) atTop (𝓝 1) := by
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).add (saturationParameter_tendsto.mul_const (density p z))).pow 2
  convert ht.inv₀ (by norm_num : ((1 : ℝ)+0*density p z)^2 ≠ 0) using 1 <;> simp [saturationCoeff]

theorem saturatedDensity_hasWeakGradient (hDensity : OrdinaryH1Density)
    {p ε : ℝ} (hp : 1 < p) (hε : 0 < ε)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) :
    HasWeakGradient (fun x => saturatedDensity p ε (u x))
      (fun x => saturationCoeff p ε (u x) • densityGradient p u U V x) := by
  let B : ℝ≥0 := ⟨p*(1+ε⁻¹), by positivity⟩
  have hf := saturatedDensity_contDiff_one hp hε.le
  have hder (z : ℂ) := (saturatedDensity_hasFDerivAt hp hε.le z).fderiv
  have hw := hasWeakGradient_bounded_complex_comp_dotH1 hDensity (B := B) hf
    (by simp [saturatedDensity,density,Real.zero_rpow (show p ≠ 0 by linarith)])
    (fun z => by rw [hder]; exact saturatedDensity_derivative_bound hp hε z) hu
  convert hw using 1
  funext x
  simp only [hder, densityGradient, smul_apply, smul_eq_mul, smul_add, smul_smul]

theorem saturatedDensity_memLp {p ε s : ℝ} (hp : 1 < p) (hε : 0 ≤ ε)
    {u : Space → ℂ} (hu : MemLp u (ENNReal.ofReal s) volume) :
    MemLp (fun x => saturatedDensity p ε (u x)) (ENNReal.ofReal (s/p)) volume := by
  apply (density_Lp (by linarith : 0 < p) hu).of_le
    ((saturatedDensity_contDiff_one hp hε).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (saturatedDensity_nonneg hε p (u x)),
    abs_of_nonneg (density_nonneg p (u x))] using saturatedDensity_le_density hε p (u x)

#print axioms saturationParameter_pos
#print axioms saturationParameter_tendsto
#print axioms saturationCoeff_continuous
#print axioms saturatedDensity_tendsto
#print axioms saturationCoeff_tendsto
#print axioms saturatedDensity_hasWeakGradient
#print axioms saturatedDensity_memLp
end HartreeF.WeakHartreeChain
