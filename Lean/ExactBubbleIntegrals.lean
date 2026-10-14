import GammaBracketMass
import SharpOrdinaryConstants
import HartreeSobolevProducer

/-! Exact Q integrals and its literal Sobolev equality from the proved
Gamma/Gaussian integral, not from an equality-case interface. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
namespace HartreeF.BubbleProfile
open Bubble SobolevStretch SharpOrdinary DirectionalCoercivity HeatRiesz

theorem bubbleC_sixthMass : (∫ x : Space, ‖bubbleC x‖^6) = Real.pi^2/4 := by
  have he (x : Space) : ‖bubbleC x‖^6 = bracketProfile 3 x := by
    simpa only [norm_bubbleC, Real.norm_eq_abs, abs_of_pos (bubble_pos x),
      show (-6/2:ℝ) = -3 by norm_num, bracketProfile] using bubble_norm_sixth x
  simp_rw [he]
  exact bracketProfile_integral_three

theorem bubbleGradient_profile_split (x : Space) :
    ‖bubbleGradient x‖^2 = bracketProfile 2 x - bracketProfile 3 x := by
  rw [bubbleGradient_norm_sq]
  unfold bracketProfile
  have he : (1+‖x‖^2)^(-2:ℝ) = (1+‖x‖^2)^(-3:ℝ)*(1+‖x‖^2) := by
    conv_rhs => rhs; rw [← Real.rpow_one (1+‖x‖^2)]
    rw [← Real.rpow_add (one_add_norm_sq_pos x)]
    norm_num
  rw [he]
  ring

theorem bubbleGradient_energy : (∫ x : Space, ‖bubbleGradient x‖^2) = 3*Real.pi^2/4 := by
  simp_rw [bubbleGradient_profile_split]
  rw [integral_sub (bracketProfile_integrable (by norm_num : (3/2:ℝ)<2))
    (bracketProfile_integrable (by norm_num : (3/2:ℝ)<3)),
    bracketProfile_integral_two, bracketProfile_integral_three]
  ring

theorem bubbleC_kinetic : kinetic bubbleGradient (fun _ => 0) = 3*Real.pi^2/4 := by
  rw [kinetic_eq_sum memLp_bubbleGradient_two
    (show MemLp (fun _ : Space => (0:Space)) 2 volume by simp), bubbleGradient_energy]
  simp

theorem bubbleC_kinetic_pos : 0 < kinetic bubbleGradient (fun _ => 0) := by
  rw [bubbleC_kinetic]
  positivity

/-- The actual Q saturates the literal squared Sobolev coefficient, proved
by exact integrals without assuming the sharp Sobolev inequality or equality. -/
theorem bubbleC_sobolev_equality :
    (eLpNorm bubbleC 6 volume).toReal^2 = sharpSobolevConstant * kinetic bubbleGradient (fun _ => 0) := by
  have hn := sixth_norm_pow_eq_integral memLp_bubbleC_six
  norm_num only [Real.rpow_ofNat] at hn
  rw [bubbleC_sixthMass] at hn
  apply (Odd.pow_inj (by decide : Odd 3)).mp
  rw [← pow_mul, show (2*3:ℕ)=6 by norm_num, hn, mul_pow,
    sharpSobolevConstant_cube, bubbleC_kinetic]
  unfold sharpSobolevSixth
  field_simp [Real.pi_ne_zero]
  ring

theorem bubbleDensity_integrable {α : ℝ} (hα : 0 < α) :
    Integrable (powerDensity α bubbleC) volume := by
  apply (bracketProfile_integrable (show (3/2:ℝ)<(3+α)/2 by linarith)).congr
  filter_upwards [] with x
  rw [powerDensity_bubbleC]
  unfold bracketProfile
  congr 1
  ring

theorem bubbleDensity_gamma_integral {α : ℝ} (hα : 0 < α) (x : Space) :
    (∫ t, gammaProfile ((3+α)/2) x t ∂positiveTimeMeasure) = powerDensity α bubbleC x := by
  rw [gammaProfile_time_integral (by linarith : 0<(3+α)/2), powerDensity_bubbleC]
  unfold bracketProfile
  congr 1
  ring

#print axioms bubbleC_sixthMass
#print axioms bubbleGradient_profile_split
#print axioms bubbleGradient_energy
#print axioms bubbleC_kinetic
#print axioms bubbleC_kinetic_pos
#print axioms bubbleC_sobolev_equality
#print axioms bubbleDensity_integrable
#print axioms bubbleDensity_gamma_integral
end HartreeF.BubbleProfile
