import ReciprocalGammaIntegral
import HeatKernelL1Pair

/-!
The normalized Riesz kernel is produced from an actual heat-time Gamma
integral at every nonzero spatial point. Positivity of the standard constant
is native. For 0<alpha<3 the zero spatial point is deliberately excluded:
its positive time integral diverges although the total real Riesz kernel is extended by zero.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace HartreeF.HeatRiesz
open GaussianFourierBridge

def standardRieszConstant (α : ℝ) : ℝ :=
  Real.Gamma ((3-α)/2) / ((2:ℝ)^α * Real.pi^(3/2:ℝ) * Real.Gamma (α/2))

def heatMixtureFactor (α : ℝ) : ℝ := (4*Real.pi)^(-(3/2:ℝ)) / Real.Gamma (α/2)

def heatMixtureIntegrand (α : ℝ) (z : Space) (t : ℝ) : ℝ :=
  t^(α/2-1) * heatKernel t z / Real.Gamma (α/2)

theorem standardRieszConstant_pos {α : ℝ} (hα : 0 < α) (hα3 : α < 3) :
    0 < standardRieszConstant α := by
  have hβ := Real.Gamma_pos_of_pos (show 0 < α/2 by linarith)
  have hγ := Real.Gamma_pos_of_pos (show 0 < (3-α)/2 by linarith)
  unfold standardRieszConstant
  positivity

theorem heatMixtureIntegrand_nonneg {α : ℝ} (hα : 0 < α)
    (z : Space) {t : ℝ} (ht : 0 < t) : 0 ≤ heatMixtureIntegrand α z t := by
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (heatKernel_nonneg ht z))
    (Real.Gamma_pos_of_pos (by linarith : 0 < α/2)).le

theorem heatMixture_eq_reciprocal (α : ℝ) (z : Space) {t : ℝ} (ht : 0 < t) :
    heatMixtureIntegrand α z t = heatMixtureFactor α *
      reciprocalGammaIntegrand ((3-α)/2) (‖z‖^2/4) t := by
  unfold heatMixtureIntegrand heatKernel heatMixtureFactor reciprocalGammaIntegrand
  rw [Real.mul_rpow (by positivity : 0 ≤ 4*Real.pi) ht.le]
  have hp : t^(α/2-1) * t^(-(3/2:ℝ)) = t^(-((3-α)/2)-1) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have he : -‖z‖^2/(4*t) = -(‖z‖^2/4)/t := by ring
  rw [he]
  calc
    _ = ((4*Real.pi)^(-(3/2:ℝ)) / Real.Gamma (α/2)) *
        (t^(α/2-1) * t^(-(3/2:ℝ))) * Real.exp (-(‖z‖^2/4)/t) := by ring
    _ = _ := by rw [hp]; ring

theorem heatMixture_integrable_nonzero {α : ℝ} (hα3 : α < 3)
    {z : Space} (hz : z ≠ 0) :
    IntegrableOn (heatMixtureIntegrand α z) (Ioi 0) := by
  have hγ : 0 < (3-α)/2 := by linarith
  have hA : 0 < ‖z‖^2/4 := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hz)) (by norm_num)
  apply ((reciprocalGamma_integrable hγ hA).const_mul (heatMixtureFactor α)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (heatMixture_eq_reciprocal α z ht).symm

theorem squared_radius_rpow (α : ℝ) {r : ℝ} (hr : 0 < r) :
    (r^2/4)^((α-3)/2) = r^(α-3) * (2:ℝ)^(3-α) := by
  rw [Real.div_rpow (sq_nonneg r) (by norm_num),
    ← Real.rpow_natCast_mul hr.le]
  have hfour : (4:ℝ) = 2^2 := by norm_num
  rw [hfour, ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have he : (2:ℝ)*((α-3)/2) = α-3 := by ring
  norm_num only [Nat.cast_ofNat] at *
  rw [he, div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 2
  ring

theorem heatMixture_normalization (α : ℝ) {r : ℝ} (hr : 0 < r) :
    heatMixtureFactor α * ((r^2/4)^(-((3-α)/2)) * Real.Gamma ((3-α)/2)) =
      standardRieszConstant α * r^(α-3) := by
  have he : -((3-α)/2) = (α-3)/2 := by ring
  rw [he, squared_radius_rpow α hr]
  have hfour : (4:ℝ)^(-(3/2:ℝ)) = (2:ℝ)^(-3:ℝ) := by
    rw [show (4:ℝ) = 2^2 by norm_num, ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hp : (2:ℝ)^(-3:ℝ) * (2:ℝ)^(3-α) = (2:ℝ)^(-α) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  unfold heatMixtureFactor
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) Real.pi_pos.le, hfour]
  calc
    _ = ((2:ℝ)^(-3:ℝ) * (2:ℝ)^(3-α)) * Real.pi^(-(3/2:ℝ)) *
        Real.Gamma ((3-α)/2) / Real.Gamma (α/2) * r^(α-3) := by ring
    _ = _ := by
      rw [hp, Real.rpow_neg (by norm_num : (0:ℝ)≤2), Real.rpow_neg Real.pi_pos.le]
      unfold standardRieszConstant
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Literal normalized heat representation, including a genuine time-integral domain. -/
theorem heatMixture_eq_riesz_nonzero {α : ℝ} (hα3 : α < 3)
    {z : Space} (hz : z ≠ 0) :
    (∫ t in Ioi 0, heatMixtureIntegrand α z t) =
      rieszKernel α (standardRieszConstant α) z := by
  have hγ : 0 < (3-α)/2 := by linarith
  have hA : 0 < ‖z‖^2/4 := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hz)) (by norm_num)
  calc
    _ = ∫ t in Ioi 0, heatMixtureFactor α *
        reciprocalGammaIntegrand ((3-α)/2) (‖z‖^2/4) t := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => heatMixture_eq_reciprocal α z ht)
    _ = heatMixtureFactor α * ((‖z‖^2/4)^(-((3-α)/2)) * Real.Gamma ((3-α)/2)) := by
      rw [integral_const_mul, reciprocalGamma_integral hγ hA]
    _ = _ := heatMixture_normalization α (norm_pos_iff.mpr hz)

#print axioms standardRieszConstant_pos
#print axioms heatMixtureIntegrand_nonneg
#print axioms heatMixture_eq_reciprocal
#print axioms heatMixture_integrable_nonzero
#print axioms squared_radius_rpow
#print axioms heatMixture_normalization
#print axioms heatMixture_eq_riesz_nonzero
end HartreeF.HeatRiesz
