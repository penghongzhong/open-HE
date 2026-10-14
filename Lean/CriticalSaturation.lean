import SaturatedDensityWeakGradient
import BoundedCompositionH1Domains
import RealSobolevApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Complete

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.CriticalSobolevBridge
open SobolevStretch StationarySelfTest WeakHartreeChain WeakHartreeProduct

theorem critical_saturation_derivative_bound {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖saturationCoeff (5/3) ε z • densityDerivative (5/3) z‖ ≤
      (5/3) * (saturatedDensity (5/3) ε z) ^ (2/5 : ℝ) := by
  let d : ℝ := 1+ε*WeakHartreeChain.density (5/3) z
  have hd : 0 < d := saturation_denominator_pos hε _ _
  have hd1 : 1 ≤ d := by
    have := mul_nonneg hε (density_nonneg (5/3) z)
    dsimp [d]
    linarith
  have hexp : (‖z‖ ^ (5/3 : ℝ)) ^ (2/5 : ℝ) = ‖z‖ ^ (2/3 : ℝ) := by
    rw [← Real.rpow_mul (norm_nonneg z)]
    norm_num
  have hden : d ^ (2/5 : ℝ) ≤ d^2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (saturationCoeff_nonneg _ _),
    densityDerivative_norm (by norm_num : (1 : ℝ) < 5/3)]
  norm_num only [show (5/3 : ℝ)-1 = 2/3 by norm_num]
  change (d^2)⁻¹ * ((5/3)*‖z‖^(2/3 : ℝ)) ≤ (5/3)*((‖z‖^(5/3 : ℝ))/d)^(2/5 : ℝ)
  rw [Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _) hd.le, hexp]
  have hh := div_le_div_of_nonneg_left (Real.rpow_nonneg (norm_nonneg z) (2/3))
    (Real.rpow_pos_of_pos hd _) hden
  convert mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 5/3 by norm_num) using 1
  ring

theorem critical_saturation_domains {ε : ℝ} (hε : 0 < ε)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) :
    MemLp (fun x => saturatedDensity (5/3) ε (u x)) 6 volume ∧
    MemLp (fun x => saturationCoeff (5/3) ε (u x) • densityGradient (5/3) u U V x) 2 volume := by
  let B : ℝ≥0 := ⟨(5/3)*(1+ε⁻¹), by positivity⟩
  have hder (z : ℂ) := (saturatedDensity_hasFDerivAt (by norm_num : (1:ℝ)<5/3) hε.le z).fderiv
  have hh := bounded_complex_composition_domains (B := B)
    (saturatedDensity_contDiff_one (by norm_num : (1:ℝ)<5/3) hε.le)
    (by simp [saturatedDensity,WeakHartreeChain.density,Real.zero_rpow (show (5/3:ℝ) ≠ 0 by norm_num)])
    (fun z => by rw [hder]; exact saturatedDensity_derivative_bound (by norm_num) hε z) hu
  refine ⟨hh.1, ?_⟩
  convert hh.2 using 1
  funext x
  simp only [complexChainGradient, hder, densityGradient, smul_apply, smul_eq_mul,
    smul_add, smul_smul]

theorem critical_saturation_gradient_bound {ε : ℝ} (hε : 0 ≤ ε)
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    ‖saturationCoeff (5/3) ε (u x) • densityGradient (5/3) u U V x‖ ≤
      (5/3) * (saturatedDensity (5/3) ε (u x)) ^ (2/5 : ℝ) * (‖U x‖ + ‖V x‖) := by
  let L := saturationCoeff (5/3) ε (u x) • densityDerivative (5/3) (u x)
  have hL := critical_saturation_derivative_bound hε (u x)
  have hc (e : ℂ) (he : ‖e‖ = 1) :
      ‖L e‖ ≤ (5/3) * (saturatedDensity (5/3) ε (u x)) ^ (2/5 : ℝ) := by
    exact (L.le_opNorm e).trans (by simpa only [he,mul_one] using hL)
  have hEq : saturationCoeff (5/3) ε (u x) • densityGradient (5/3) u U V x =
      L 1 • U x + L Complex.I • V x := by
    simp only [L,densityGradient,smul_add,smul_smul,smul_apply,smul_eq_mul]
  rw [hEq]
  calc
    _ ≤ ‖L 1 • U x‖ + ‖L Complex.I • V x‖ := norm_add_le _ _
    _ = ‖L 1‖*‖U x‖ + ‖L Complex.I‖*‖V x‖ := by rw [norm_smul,norm_smul]
    _ ≤ ((5/3)*(saturatedDensity (5/3) ε (u x))^(2/5:ℝ))*‖U x‖ +
      ((5/3)*(saturatedDensity (5/3) ε (u x))^(2/5:ℝ))*‖V x‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (hc 1 (by simp)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hc Complex.I (by simp)) (norm_nonneg _))
    _ = _ := by ring

#print axioms critical_saturation_gradient_bound

#print axioms critical_saturation_derivative_bound
#print axioms critical_saturation_domains
end HartreeF.CriticalSobolevBridge
