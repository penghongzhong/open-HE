import BubblePotentialTriple
import SharpOrdinaryInterfaces

/-! The actual Riesz action on Q^(3+alpha), computed from the independently
proved positive Gaussian-rate triple integral. No HLS equality or potential
formula is a premise. The physical domains include every fixed x. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
namespace HartreeF.BubbleProfile
open HeatRiesz Bubble SobolevStretch DirectionalCoercivity PressureDomain

def bubblePotentialConstant (α : ℝ) : ℝ :=
  Real.Gamma ((3-α)/2)/((2:ℝ)^α * Real.Gamma ((3+α)/2))

theorem bubblePotentialConstant_pos {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    0<bubblePotentialConstant α := by
  have ha := Real.Gamma_pos_of_pos (show 0<(3-α)/2 by linarith)
  have hb := Real.Gamma_pos_of_pos (show 0<(3+α)/2 by linarith)
  unfold bubblePotentialConstant
  positivity

/-- Literal pointwise standard-Riesz convolution formula, at every x including0. -/
theorem bubble_potential_exact {α : ℝ} (hα : 0<α) (hα3 : α<3) (x : Space) :
    potential α (standardRieszConstant α) bubbleC x =
      bubblePotentialConstant α * bracketProfile ((3-α)/2) x := by
  rw [bubble_potential_parameter_identity hα hα3 x,
    parameterKernel_integral (show 0<(3-α)/2 by linarith)
      (show (3-α)/2<3/2 by linarith) (sq_nonneg ‖x‖)]
  rw [show (3/2:ℝ)-(3-α)/2 = α/2 by ring]
  have hγ := (Real.Gamma_pos_of_pos (show 0<α/2 by linarith)).ne'
  have hb := (Real.Gamma_pos_of_pos (show 0<(3+α)/2 by linarith)).ne'
  have hp := (Real.rpow_pos_of_pos Real.pi_pos (3/2:ℝ)).ne'
  have htwo := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) α).ne'
  unfold bubbleTripleCoefficient rieszWeightDenom bubblePotentialConstant bracketProfile
  field_simp

theorem bubble_potential_power {α : ℝ} (hα : 0<α) (hα3 : α<3) (x : Space) :
    potential α (standardRieszConstant α) bubbleC x =
      bubblePotentialConstant α * (bubble x)^(3-α) := by
  rw [bubble_potential_exact hα hα3]
  congr 1
  unfold bracketProfile bubble
  rw [← Real.rpow_mul (one_add_norm_sq_pos x).le]
  congr 1
  ring

theorem bubble_interaction_integrand {α : ℝ} (hα : 0<α) (hα3 : α<3) (x : Space) :
    potential α (standardRieszConstant α) bubbleC x * powerDensity α bubbleC x =
      bubblePotentialConstant α * ‖bubbleC x‖^6 := by
  rw [bubble_potential_power hα hα3, powerDensity, norm_bubbleC,
    mul_assoc, ← Real.rpow_add (bubble_pos x)]
  rw [show (3-α)+(3+α) = (6:ℝ) by ring]
  norm_num only [Real.rpow_ofNat]

theorem bubble_interaction_integrable {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    Integrable (fun x => potential α (standardRieszConstant α) bubbleC x * powerDensity α bubbleC x)
      volume := by
  apply ((memLp_bubbleC_six.integrable_norm_pow (by decide : (6:ℕ)≠0)).const_mul
    (bubblePotentialConstant α)).congr
  exact Eventually.of_forall (fun x => (bubble_interaction_integrand hα hα3 x).symm)

theorem bubble_interaction_exact {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    interaction α bubbleC = bubblePotentialConstant α * Real.pi^2/4 := by
  unfold interaction
  simp_rw [bubble_interaction_integrand hα hα3]
  rw [integral_const_mul, bubbleC_sixthMass]
  ring

theorem bubble_rieszPair_nonneg {α : ℝ} (hα : 0<α) (hα3 : α<3) (q : Space × Space) :
    0≤rieszPairDensity α (standardRieszConstant α) bubbleC q := by
  have hc := standardRieszConstant_pos hα hα3
  unfold rieszPairDensity rieszKernel powerDensity
  positivity

/-- The literal six-dimensional Riesz pair is absolutely integrable without
an HLS premise, using the newly evaluated and integrable potential density. -/
theorem bubble_rieszPair_integrable {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    Integrable (rieszPairDensity α (standardRieszConstant α) bubbleC) (volume.prod volume) := by
  have hm : AEStronglyMeasurable (rieszPairDensity α (standardRieszConstant α) bubbleC)
      (volume.prod volume) := by
    apply Measurable.aestronglyMeasurable
    unfold rieszPairDensity rieszKernel powerDensity bubbleC bubble
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Eventually.of_forall (fun x => (bubble_potential_integrable hα hα3 x).mul_const
      (powerDensity α bubbleC x))
  · apply (bubble_interaction_integrable hα hα3).congr
    filter_upwards [] with x
    have he : (fun y => ‖rieszPairDensity α (standardRieszConstant α) bubbleC (x,y)‖) =
        (fun y => rieszPairDensity α (standardRieszConstant α) bubbleC (x,y)) := by
      funext y
      exact Real.norm_of_nonneg (bubble_rieszPair_nonneg hα hα3 (x,y))
    rw [he]
    unfold rieszPairDensity
    dsimp only
    rw [integral_mul_const]
    rfl

theorem bubble_rieszPair_integral {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    (∫ q, rieszPairDensity α (standardRieszConstant α) bubbleC q ∂volume.prod volume) =
      interaction α bubbleC := by
  rw [integral_prod _ (bubble_rieszPair_integrable hα hα3)]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold rieszPairDensity potential
  dsimp only
  rw [integral_mul_const]

#print axioms bubblePotentialConstant_pos
#print axioms bubble_potential_exact
#print axioms bubble_potential_power
#print axioms bubble_interaction_integrand
#print axioms bubble_interaction_integrable
#print axioms bubble_interaction_exact
#print axioms bubble_rieszPair_nonneg
#print axioms bubble_rieszPair_integrable
#print axioms bubble_rieszPair_integral
end HartreeF.BubbleProfile
