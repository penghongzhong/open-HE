import ExactBubblePotential
import ExactHartreeSobolevComposition

/-! Exact calibration of the physical bubble, the literal sharp ordinary
constants, and the normalized amplitude. Every identity is proved from
Gamma, logarithm, and real-power algebra; no inequality or optimizer is
assumed. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.BubbleProfile
open HeatRiesz Bubble SobolevStretch DirectionalCoercivity SharpOrdinary

/-- The independently evaluated sixth mass of the unit bubble. -/
def bubbleMassConstant : ℝ := Real.pi^2/4

/-- The positive amplitude that makes the physical Q equation normalized. -/
def bubbleAmplitude (α : ℝ) : ℝ :=
  (3 / bubblePotentialConstant α)^((4+2*α)⁻¹)

theorem bubbleMassConstant_pos : 0 < bubbleMassConstant := by
  unfold bubbleMassConstant
  positivity

theorem bubble_mass_rpow_factor (α : ℝ) :
    (Real.pi^(α/2))⁻¹ * (4/Real.sqrt Real.pi)^(α/3) =
      bubbleMassConstant^(-α/3) := by
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (Real.rpow_pos_of_pos bubbleMassConstant_pos _)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_inv,
    Real.log_rpow Real.pi_pos, Real.log_rpow (by positivity),
    Real.log_rpow bubbleMassConstant_pos, Real.log_div (by norm_num) (by positivity),
    Real.log_sqrt Real.pi_pos.le]
  unfold bubbleMassConstant
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]
  push_cast
  ring

theorem sharpHLSConstant_eq_bubbleMass (α : ℝ) :
    sharpHLSConstant α = bubblePotentialConstant α * bubbleMassConstant^(-α/3) := by
  rw [← bubble_mass_rpow_factor]
  unfold sharpHLSConstant bubblePotentialConstant
  ring

theorem sharpSobolevConstant_eq_bubbleMass :
    sharpSobolevConstant = (1/3:ℝ) * bubbleMassConstant^(-2/3:ℝ) := by
  unfold sharpSobolevConstant
  rw [show 4/Real.pi^2 = bubbleMassConstant⁻¹ by unfold bubbleMassConstant; simp]
  rw [← Real.rpow_neg_eq_inv_rpow]
  congr 2
  norm_num

theorem bubble_combinedConstant_eq {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    standardCombinedConstant α = bubblePotentialConstant α * bubbleMassConstant *
      (3*bubbleMassConstant)^(-(3+α)) := by
  have hk := bubblePotentialConstant_pos hα hα3
  have hm := bubbleMassConstant_pos
  apply Real.log_injOn_pos (standardCombinedConstant_pos hα hα3) (by simp only [Set.mem_Ioi]; positivity)
  rw [standardCombinedConstant, sharpHLSConstant_eq_bubbleMass,
    sharpSobolevConstant_eq_bubbleMass]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul hk.ne' (by positivity), Real.log_rpow hm,
    Real.log_rpow (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow hm, Real.log_div (by norm_num) (by norm_num), Real.log_one,
    Real.log_mul (by positivity) (by positivity), Real.log_mul hk.ne' hm.ne',
    Real.log_rpow (by positivity), Real.log_mul (by norm_num) hm.ne']
  ring

/-- The actual interaction of Q attains the literal combined constant. -/
theorem bubble_combined_equality {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    interaction α bubbleC = standardCombinedConstant α *
      (kinetic bubbleGradient (fun _ => 0))^(3+α) := by
  rw [bubble_interaction_exact hα hα3, bubbleC_kinetic, bubble_combinedConstant_eq hα hα3]
  rw [show 3*Real.pi^2/4 = 3*bubbleMassConstant by unfold bubbleMassConstant; ring,
    mul_assoc, ← Real.rpow_add (mul_pos (by norm_num) bubbleMassConstant_pos)]
  rw [neg_add_cancel, Real.rpow_zero, mul_one]
  unfold bubbleMassConstant
  ring

theorem bubbleAmplitude_pos {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    0 < bubbleAmplitude α := by
  unfold bubbleAmplitude
  exact Real.rpow_pos_of_pos (div_pos (by norm_num) (bubblePotentialConstant_pos hα hα3)) _

theorem bubbleAmplitude_rpow {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    (bubbleAmplitude α)^(4+2*α) = 3/bubblePotentialConstant α := by
  have hk := bubblePotentialConstant_pos hα hα3
  unfold bubbleAmplitude
  rw [← Real.rpow_mul (by positivity : 0 ≤ 3/bubblePotentialConstant α),
    inv_mul_cancel₀ (by linarith : 4+2*α ≠ 0), Real.rpow_one]

theorem bubbleAmplitude_balance {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    bubblePotentialConstant α * (bubbleAmplitude α)^(4+2*α) = 3 := by
  rw [bubbleAmplitude_rpow hα hα3]
  field_simp [(bubblePotentialConstant_pos hα hα3).ne']

/-- The normalized bubble has exactly the explicit product-constant threshold
as its kinetic energy. This calibration needs neither sharp inequality. -/
theorem bubbleAmplitude_kinetic_eq_threshold {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    (bubbleAmplitude α)^2 * (3*Real.pi^2/4) = standardCombinedThreshold α := by
  have hk := bubblePotentialConstant_pos hα hα3
  have hm := bubbleMassConstant_pos
  have ha := bubbleAmplitude_pos hα hα3
  have hfour : 4+2*α ≠ 0 := by linarith
  have hp : 1-(3+α) ≠ 0 := by linarith
  apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity) (standardCombinedThreshold_pos hα hα3)
  rw [show 3*Real.pi^2/4 = 3*bubbleMassConstant by unfold bubbleMassConstant; ring,
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by norm_num) hm.ne']
  unfold bubbleAmplitude standardCombinedThreshold
  rw [Real.log_rpow (by positivity), Real.log_div (by norm_num) hk.ne',
    Real.log_rpow (standardCombinedConstant_pos hα hα3), bubble_combinedConstant_eq hα hα3,
    Real.log_mul (by positivity) (by positivity), Real.log_mul hk.ne' hm.ne',
    Real.log_rpow (by positivity), Real.log_mul (by norm_num) hm.ne']
  push_cast
  field_simp [hfour, hp]
  ring

#print axioms bubbleMassConstant_pos
#print axioms bubble_mass_rpow_factor
#print axioms sharpHLSConstant_eq_bubbleMass
#print axioms sharpSobolevConstant_eq_bubbleMass
#print axioms bubble_combinedConstant_eq
#print axioms bubble_combined_equality
#print axioms bubbleAmplitude_pos
#print axioms bubbleAmplitude_rpow
#print axioms bubbleAmplitude_balance
#print axioms bubbleAmplitude_kinetic_eq_threshold
end HartreeF.BubbleProfile
