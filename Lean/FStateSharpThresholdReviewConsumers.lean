import FStateSharpGroundThreshold

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.StateSharpThresholdReview
open EnergySpace StateEnergy EnergyVariation SobolevStretch ForcingDomain HeatRiesz
open SharpOrdinary DirectionalCoercivity StationarySelfTest BubbleProfile StateSharpThreshold
attribute [local irreducible] energySubmodule

/-- Every actual least-energy weak stationary state has the same kinetic and
energy levels as the explicit W after transport to the current C43 state. -/
theorem canonical_groundState_levels {alpha : ℝ} {w : Space → ℂ} {WRe WIm : Space → Space}
    (hw : IsGroundState alpha w WRe WIm)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density) :
    gradientSquared (inDotEnergyState hw.stationary.sobolev) =
      gradientSquared (normalizedBubbleState alpha) ∧
    totalEnergy alpha (inDotEnergyState hw.stationary.sobolev) =
      totalEnergy alpha (normalizedBubbleState alpha) := by
  constructor
  · rw [gradientSquared_inDotEnergyState,
      normalizedBubbleState_kinetic hH.order_pos hH.order_lt_three]
    exact groundState_kinetic_eq_standard hw hOrd hH hS hDensity
  · rw [totalEnergy_inDotEnergyState, normalizedBubbleState_energy hOrd hH hS hDensity]
    exact groundState_energy_eq_standard hw hOrd hH hS hDensity

/-- The exact inverse coercivity factor reaches the actual W kinetic level. -/
theorem normalizedBubbleState_scaled_energy {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density) :
    (2*(3+alpha)/(2+alpha)) * totalEnergy alpha (normalizedBubbleState alpha) =
      gradientSquared (normalizedBubbleState alpha) := by
  rw [normalizedBubbleState_energy hOrd hH hS hDensity,
    normalizedBubbleState_kinetic hH.order_pos hH.order_lt_three]
  unfold thresholdEnergy
  have h2 : 2+alpha ≠ 0 := by linarith [hH.order_pos]
  have h3 : 3+alpha ≠ 0 := by linarith [hH.order_pos]
  field_simp

/-- At the literal W kinetic boundary the actual energy cannot lie below E(W).
This is a static barrier; no flow or conserved energy is an input or conclusion. -/
theorem energy_barrier_at_W {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density)
    (u : EnergyState) (hA : gradientSquared u = gradientSquared (normalizedBubbleState alpha)) :
    totalEnergy alpha (normalizedBubbleState alpha) ≤ totalEnergy alpha u := by
  have h := state_kinetic_le_energy_below_W hOrd hH hS u hA.le
  rw [hA, ← normalizedBubbleState_scaled_energy hOrd hH hS hDensity] at h
  have hc : 0 < 2*(3+alpha)/(2+alpha) :=
    div_pos (by linarith [hH.order_pos]) (by linarith [hH.order_pos])
  nlinarith

/-- An actual strict energy gap excludes the W kinetic boundary. -/
theorem strict_energy_excludes_W_boundary {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density)
    (u : EnergyState)
    (hE : totalEnergy alpha u < totalEnergy alpha (normalizedBubbleState alpha)) :
    gradientSquared u ≠ gradientSquared (normalizedBubbleState alpha) := by
  intro hA
  exact (not_lt_of_ge (energy_barrier_at_W hOrd hH hS hDensity u hA)) hE

/-- Strict energy gap upgrades the closed sub-W kinetic region to a concrete
strict margin using the actual C43 energy and original bubble. -/
theorem strict_static_kinetic_margin {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density)
    (u : EnergyState)
    (hA : gradientSquared u ≤ gradientSquared (normalizedBubbleState alpha))
    (hE : totalEnergy alpha u < totalEnergy alpha (normalizedBubbleState alpha)) :
    gradientSquared u ≤ (2*(3+alpha)/(2+alpha)) * totalEnergy alpha u ∧
      (2*(3+alpha)/(2+alpha)) * totalEnergy alpha u <
        gradientSquared (normalizedBubbleState alpha) := by
  refine ⟨state_kinetic_le_energy_below_W hOrd hH hS u hA, ?_⟩
  rw [← normalizedBubbleState_scaled_energy hOrd hH hS hDensity]
  exact mul_lt_mul_of_pos_left hE (div_pos (by linarith [hH.order_pos])
    (by linarith [hH.order_pos]))

/-- The genuine zero subtype state has exactly zero kinetic energy. -/
theorem canonical_zero_kinetic : gradientSquared (0 : EnergyState) = 0 := by
  simp [gradientSquared]

/-- The zero L6 representative is used only through its a.e. class. -/
theorem canonical_zero_energy {alpha : ℝ} (ha : 0 < alpha) :
    totalEnergy alpha (0 : EnergyState) = 0 := by
  unfold totalEnergy interactionLp
  rw [canonical_zero_kinetic, map_zero,
    interaction_congr_ae alpha (Lp.coeFn_zero ℂ 6 volume)]
  have hp : 3+alpha ≠ 0 := by linarith
  simp [interaction, HartreeF.powerDensity, Real.zero_rpow hp]

/-- Zero lies strictly inside both actual W bounds, without an L2 value assumption. -/
theorem canonical_zero_strictly_below_W {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density) :
    gradientSquared (0 : EnergyState) < gradientSquared (normalizedBubbleState alpha) ∧
    totalEnergy alpha (0 : EnergyState) < totalEnergy alpha (normalizedBubbleState alpha) := by
  rw [canonical_zero_kinetic, canonical_zero_energy hH.order_pos,
    normalizedBubbleState_kinetic hH.order_pos hH.order_lt_three,
    normalizedBubbleState_energy hOrd hH hS hDensity]
  have hG := standardCombinedThreshold_pos hH.order_pos hH.order_lt_three
  exact ⟨hG, mul_pos (div_pos (by linarith [hH.order_pos])
    (by linarith [hH.order_pos])) hG⟩

/-- The zero boundary of coercivity is nonvacuous: below W, nonpositive energy
forces the actual canonical state itself to vanish. -/
theorem state_eq_zero_of_nonpositive_energy_below_W {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) (u : EnergyState)
    (hA : gradientSquared u ≤ gradientSquared (normalizedBubbleState alpha))
    (hE : totalEnergy alpha u ≤ 0) : u = 0 := by
  have h := state_kinetic_le_energy_below_W hOrd hH hS u hA
  have hc : 0 ≤ 2*(3+alpha)/(2+alpha) :=
    (div_pos (by linarith [hH.order_pos]) (by linarith [hH.order_pos])).le
  have hz : gradientSquared u = 0 := le_antisymm
    (h.trans (by simpa using mul_le_mul_of_nonneg_left hE hc)) (gradientSquared_nonneg u)
  apply (pureGradientNorm_eq_zero_iff hS.ordinary u).mp
  simp [pureGradientNorm, hz]

#print axioms canonical_groundState_levels
#print axioms normalizedBubbleState_scaled_energy
#print axioms energy_barrier_at_W
#print axioms strict_energy_excludes_W_boundary
#print axioms strict_static_kinetic_margin
#print axioms canonical_zero_kinetic
#print axioms canonical_zero_energy
#print axioms canonical_zero_strictly_below_W
#print axioms state_eq_zero_of_nonpositive_energy_below_W
end HartreeF.StateSharpThresholdReview
