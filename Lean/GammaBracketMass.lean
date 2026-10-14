import GammaBracketProfile
import GaussianProfileConvolution

/-! Exact spatial profile integrals from a proved nonnegative Gamma/Gaussian
joint L1 domain and genuine Fubini, on actual Euclidean R3. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
namespace HartreeF.BubbleProfile
open HeatRiesz

theorem gammaProfile_space_integral (s : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ x : Space, gammaProfile s x t) =
      (Real.pi^(3/2:ℝ)/Real.Gamma s) *
        (t^((s-3/2)-1)*Real.exp (-t)) := by
  simp_rw [gammaProfile_factor]
  rw [integral_const_mul, gaussian_mass_integral ht,
    Real.div_rpow Real.pi_pos.le ht.le]
  have he : t^(s-1)/t^(3/2:ℝ) = t^((s-3/2)-1) := by
    rw [← Real.rpow_sub ht]
    congr 1
    ring
  calc
    _ = (Real.pi^(3/2:ℝ)/Real.Gamma s) *
        (t^(s-1)/t^(3/2:ℝ)) * Real.exp (-t) := by ring
    _ = _ := by rw [he]; ring

/-- Exact integral of (1+|x|^2)^(-s), with its genuine domain proved separately. -/
theorem bracketProfile_integral {s : ℝ} (hs : 3/2 < s) :
    (∫ x : Space, bracketProfile s x) =
      Real.pi^(3/2:ℝ) * Real.Gamma (s-3/2) / Real.Gamma s := by
  have hs0 : 0 < s := by linarith
  have hγ : 0 < s-3/2 := sub_pos.mpr hs
  have hp := gammaProfile_joint_integrable hs
  have hg : (∫ t, t^((s-3/2)-1)*Real.exp (-t) ∂positiveTimeMeasure) = Real.Gamma (s-3/2) := by
    simpa only [positiveTimeMeasure, one_div, inv_one, Real.one_rpow, one_mul]
      using (Real.integral_rpow_mul_exp_neg_mul_Ioi hγ (by norm_num : (0:ℝ)<1))
  calc
    _ = ∫ x : Space, (∫ t, gammaProfile s x t ∂positiveTimeMeasure) :=
      integral_congr_ae (Eventually.of_forall (fun x => (gammaProfile_time_integral hs0 x).symm))
    _ = ∫ p : Space × ℝ, gammaProfile s p.1 p.2 ∂volume.prod positiveTimeMeasure :=
      (integral_prod _ hp).symm
    _ = ∫ t, (∫ x : Space, gammaProfile s x t) ∂positiveTimeMeasure :=
      integral_prod_symm _ hp
    _ = ∫ t, (Real.pi^(3/2:ℝ)/Real.Gamma s) *
        (t^((s-3/2)-1)*Real.exp (-t)) ∂positiveTimeMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact gammaProfile_space_integral s ht
    _ = _ := by rw [integral_const_mul, hg]; ring

theorem pi_three_halves_mul_sqrt : Real.pi^(3/2:ℝ)*Real.sqrt Real.pi = Real.pi^2 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add Real.pi_pos]
  norm_num

theorem gamma_three_halves : Real.Gamma (3/2:ℝ) = Real.sqrt Real.pi/2 := by
  rw [show (3/2:ℝ) = 1/2+1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0), Real.Gamma_one_half_eq]
  ring

theorem bracketProfile_integral_two : (∫ x : Space, bracketProfile 2 x) = Real.pi^2 := by
  rw [bracketProfile_integral (by norm_num : (3/2:ℝ)<2)]
  norm_num
  rw [Real.Gamma_one_half_eq]
  exact pi_three_halves_mul_sqrt

theorem bracketProfile_integral_three : (∫ x : Space, bracketProfile 3 x) = Real.pi^2/4 := by
  rw [bracketProfile_integral (by norm_num : (3/2:ℝ)<3)]
  norm_num
  rw [gamma_three_halves]
  calc
    _ = (Real.pi^(3/2:ℝ)*Real.sqrt Real.pi)/4 := by ring
    _ = _ := by rw [pi_three_halves_mul_sqrt]

#print axioms gammaProfile_space_integral
#print axioms bracketProfile_integral
#print axioms pi_three_halves_mul_sqrt
#print axioms gamma_three_halves
#print axioms bracketProfile_integral_two
#print axioms bracketProfile_integral_three
end HartreeF.BubbleProfile
