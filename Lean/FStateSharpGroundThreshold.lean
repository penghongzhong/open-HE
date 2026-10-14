import NormalizedBubbleGroundState
import FStateEnergyConsumers
import FSharpEnergyBarrier

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.StateSharpThreshold
open EnergySpace StateEnergy EnergyVariation SobolevStretch ForcingDomain HeatRiesz
open SharpOrdinary DirectionalCoercivity StationarySelfTest BubbleProfile
attribute [local irreducible] energySubmodule

/-- The canonical state retains the original two-real-gradient kinetic energy. -/
theorem gradientSquared_inDotEnergyState {u : Space → ℂ} {U V : Space → Space}
    (hu : InDotH1 u U V) : gradientSquared (inDotEnergyState hu) = kinetic U V := by
  rw [← state_kinetic_eq_gradientSquared]
  unfold kinetic
  apply integral_congr_ae
  filter_upwards [inDotEnergyState_real_gradient_ae hu,
    inDotEnergyState_imag_gradient_ae hu] with x hre him
  simp only [complexGradient, hre, him]

/-- Canonicalization preserves the literal Hartree energy, with no value-L2
hypothesis or additional regularity premise. -/
theorem totalEnergy_inDotEnergyState (alpha : ℝ) {u : Space → ℂ} {U V : Space → Space}
    (hu : InDotH1 u U V) : totalEnergy alpha (inDotEnergyState hu) = energy alpha u U V := by
  unfold totalEnergy energy interactionLp
  rw [gradientSquared_inDotEnergyState hu,
    interaction_congr_ae alpha (inDotEnergyState_value_ae hu)]

/-- The explicit genuine weak stationary W, in the same Banach energy space
used for the actual mild trajectory. -/
def normalizedBubbleState (alpha : ℝ) : EnergyState :=
  inDotEnergyState (normalizedBubble_inDotH1 alpha)

theorem normalizedBubbleState_value_ae (alpha : ℝ) :
    (energyValue (normalizedBubbleState alpha) : Space → ℂ) =ᵐ[volume] normalizedBubble alpha :=
  inDotEnergyState_value_ae (normalizedBubble_inDotH1 alpha)

theorem normalizedBubbleState_kinetic {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3) :
    gradientSquared (normalizedBubbleState alpha) = standardCombinedThreshold alpha := by
  rw [normalizedBubbleState, gradientSquared_inDotEnergyState]
  exact normalizedBubble_kinetic_eq_threshold ha ha3

theorem normalizedBubbleState_energy {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density) :
    totalEnergy alpha (normalizedBubbleState alpha) =
      thresholdEnergy alpha (standardCombinedThreshold alpha) := by
  rw [normalizedBubbleState, totalEnergy_inDotEnergyState]
  exact groundState_energy_eq_standard (normalizedBubble_isGroundState hOrd hH hS hDensity)
    hOrd hH hS hDensity

/-- The sharp normalized inequality is produced from the standard sharp
interfaces on the actual state's full weak-gradient domain. It is not assumed
as a Hartree-specific internal premise. -/
theorem state_sharp_interaction_bound {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (u : EnergyState) :
    interactionLp alpha (energyValue u) ≤ (standardCombinedThreshold alpha)^(1-(3+alpha)) *
      (gradientSquared u)^(3+alpha) := by
  have h := (exact_normalized_hartree_sobolev hOrd hH hS).bound (energyState_inDotH1 u)
  simpa only [state_kinetic_eq_gradientSquared, interactionLp] using h

/-- Static kinetic coercivity below the original explicit W level in the
actual energy state. A dynamic application must still supply conservation
and continuity from the genuine mild trajectory. -/
theorem state_kinetic_le_energy_below_W {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (u : EnergyState)
    (hA : gradientSquared u ≤ gradientSquared (normalizedBubbleState alpha)) :
    gradientSquared u ≤ (2*(3+alpha)/(2+alpha)) * totalEnergy alpha u := by
  have hAG : gradientSquared u ≤ standardCombinedThreshold alpha :=
    hA.trans_eq (normalizedBubbleState_kinetic hH.order_pos hH.order_lt_three)
  have h := EnergyTrapping.kinetic_le_energy (p := 3+alpha)
    (by linarith [hH.order_pos])
    (standardCombinedThreshold_pos hH.order_pos hH.order_lt_three)
    (gradientSquared_nonneg u) hAG (state_sharp_interaction_bound hOrd hH hS u)
    (rfl : totalEnergy alpha u = gradientSquared u/2 -
      interactionLp alpha (energyValue u)/(2*(3+alpha)))
  simpa only [show 3+alpha-1 = 2+alpha by ring] using h

#print axioms gradientSquared_inDotEnergyState
#print axioms totalEnergy_inDotEnergyState
#print axioms normalizedBubbleState
#print axioms normalizedBubbleState_value_ae
#print axioms normalizedBubbleState_kinetic
#print axioms normalizedBubbleState_energy
#print axioms state_sharp_interaction_bound
#print axioms state_kinetic_le_energy_below_W
end HartreeF.StateSharpThreshold
