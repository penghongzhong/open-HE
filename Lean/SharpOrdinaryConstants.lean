import HeatRieszPointwise

/-!
Explicit three-dimensional ordinary sharp HLS and Sobolev constants.

The primary HLS factor is the specialization of Frank--Lieb,
arXiv:1010.5821v3, equation (1.1), to N = 3 and lambda = 3 - alpha.
Multiplication by the already native standard Riesz normalization yields
`sharpHLSConstant`. The squared Sobolev coefficient is the N = 3
specialization of equation (1.4). This module proves constant algebra and
positivity only; it does not postulate or prove either analytic inequality.
-/
noncomputable section
set_option autoImplicit false

namespace HartreeF.SharpOrdinary

/-- Sharp HLS coefficient for the standard normalized Riesz kernel in R^3. -/
def sharpHLSConstant (α : ℝ) : ℝ :=
  Real.Gamma ((3 - α) / 2) /
    ((2 : ℝ) ^ α * Real.pi ^ (α / 2) * Real.Gamma ((3 + α) / 2)) *
    (4 / Real.sqrt Real.pi) ^ (α / 3)

/-- Literal primary-source HLS coefficient for the unnormalized kernel. -/
def primaryHLSFactor (α : ℝ) : ℝ :=
  Real.pi ^ ((3 - α) / 2) * Real.Gamma (α / 2) /
    Real.Gamma ((3 + α) / 2) *
    (Real.Gamma 3 / Real.Gamma (3 / 2)) ^ (α / 3)

/-- Sharp coefficient in the squared L^6 Sobolev estimate in R^3. -/
def sharpSobolevConstant : ℝ := (1 / 3 : ℝ) * (4 / Real.pi ^ 2) ^ (2 / 3 : ℝ)

/-- Corresponding coefficient in the sixth-power Sobolev estimate. -/
def sharpSobolevSixth : ℝ := 16 / (27 * Real.pi ^ 4)

theorem sharpHLSConstant_pos {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    0 < sharpHLSConstant α := by
  have hminus := Real.Gamma_pos_of_pos (show 0 < (3 - α) / 2 by linarith)
  have hplus := Real.Gamma_pos_of_pos (show 0 < (3 + α) / 2 by linarith)
  unfold sharpHLSConstant
  positivity

theorem primaryHLSFactor_pos {α : ℝ} (hα : 0 < α) :
    0 < primaryHLSFactor α := by
  have hαhalf := Real.Gamma_pos_of_pos (show 0 < α / 2 by linarith)
  have hplus := Real.Gamma_pos_of_pos (show 0 < (3 + α) / 2 by linarith)
  have hthree := Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 by norm_num)
  have hthreehalf := Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  unfold primaryHLSFactor
  positivity

theorem sharpSobolevConstant_pos : 0 < sharpSobolevConstant := by
  unfold sharpSobolevConstant
  positivity

theorem sharpSobolevSixth_pos : 0 < sharpSobolevSixth := by
  unfold sharpSobolevSixth
  positivity

theorem sharpSobolevConstant_cube : sharpSobolevConstant ^ 3 = sharpSobolevSixth := by
  unfold sharpSobolevConstant sharpSobolevSixth
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 4 / Real.pi ^ 2)]
  norm_num
  ring

theorem primary_gamma_ratio : Real.Gamma 3 / Real.Gamma (3 / 2) =
    4 / Real.sqrt Real.pi := by
  have hthree : Real.Gamma 3 = 2 := by
    simp
  have hthreehalf : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    have hrec := Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)
    rw [Real.Gamma_one_half_eq] at hrec
    convert hrec using 1 <;> norm_num
    ring
  rw [hthree, hthreehalf]
  ring

/-- The literal primary HLS coefficient has the chosen native Riesz normalization. -/
theorem sharpHLSConstant_eq_riesz_factor {α : ℝ} (hα : 0 < α) :
    sharpHLSConstant α = HartreeF.HeatRiesz.standardRieszConstant α *
      primaryHLSFactor α := by
  have hgamma : Real.Gamma (α / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (show 0 < α / 2 by linarith)).ne'
  have hpi : Real.pi ^ ((3 - α) / 2) / Real.pi ^ (3 / 2 : ℝ) =
      1 / Real.pi ^ (α / 2) := by
    rw [← Real.rpow_sub Real.pi_pos]
    rw [show (3 - α) / 2 - (3 / 2 : ℝ) = -(α / 2) by ring]
    rw [Real.rpow_neg Real.pi_pos.le, one_div]
  unfold sharpHLSConstant HartreeF.HeatRiesz.standardRieszConstant primaryHLSFactor
  rw [primary_gamma_ratio]
  symm
  calc
    _ = (Real.Gamma ((3 - α) / 2) /
        ((2 : ℝ) ^ α * Real.Gamma ((3 + α) / 2))) *
        (Real.pi ^ ((3 - α) / 2) / Real.pi ^ (3 / 2 : ℝ)) *
        (4 / Real.sqrt Real.pi) ^ (α / 3) := by
      field_simp
    _ = _ := by rw [hpi]; ring

/-- Literal N=3 coefficient from Frank--Lieb Eq(1.4) is the inverse
of the stated squared-norm Sobolev coefficient. -/
theorem sharpSobolevConstant_primary :
    ((3:ℝ)/4) * (2*Real.pi^2)^(2/3:ℝ) * sharpSobolevConstant = 1 := by
  have hp : (2*Real.pi^2)*(4/Real.pi^2) = (8:ℝ) := by
    field_simp
    ring
  unfold sharpSobolevConstant
  calc
    _ = (1/4:ℝ) * ((2*Real.pi^2)^(2/3:ℝ) * (4/Real.pi^2)^(2/3:ℝ)) := by ring
    _ = (1/4:ℝ) * (8:ℝ)^(2/3:ℝ) := by
      rw [← Real.mul_rpow (by positivity : 0 ≤ 2*Real.pi^2)
        (by positivity : 0 ≤ 4/Real.pi^2), hp]
    _ = 1 := by
      rw [show (8:ℝ) = 2^3 by norm_num,
        ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num

#print axioms sharpHLSConstant_pos
#print axioms primaryHLSFactor_pos
#print axioms sharpSobolevConstant_pos
#print axioms sharpSobolevSixth_pos
#print axioms sharpSobolevConstant_cube
#print axioms primary_gamma_ratio
#print axioms sharpHLSConstant_eq_riesz_factor

#print axioms sharpSobolevConstant_primary

end HartreeF.SharpOrdinary
