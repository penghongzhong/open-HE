import FConditionalLowMassRecovery

/-! Same original value and actual weak gradient, with an explicit conditional
mass budget. No path continuity, conservation, decay, or Hartree-input producer
is asserted by this pointwise endpoint component. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal Topology
namespace HartreeF.MassRecovery
open Retarded EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest

variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
variable {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
variable (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
variable (t : ℝ) (u : EnergyState) (F : EndpointOne) (G : EndpointSource)
variable (hG : ∀ᵐ s ∂volume.restrict (Ici t),
  Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
variable (hNW : OriginalScalarNoWaste σ t u F)
include hDensity hSob hE hL hσ hG hNW

theorem recoveredValueL2_derivative (j : Fin 3) :
    ∂_{coordinate j} (Lp.toTemperedDistribution
      (recoveredValueL2 hDensity hSob hE q hL hσ t u G)) =
      Lp.toTemperedDistribution (energyGradient j u) := by
  rw [recoveredValueL2_distribution hDensity hSob hE q hL hσ t u F G hG hNW]
  exact energyDistribution_derivative u j

theorem recoveredValueL2_actual_weak_gradient (A : ℂ →L[ℝ] ℝ) :
    HasWeakGradient (fun x => A (recoveredValueL2 hDensity hSob hE q hL hσ t u G x))
      (energyProjectedGradient A u) :=
  l2_hasWeakGradient _ _
    (recoveredValueL2_derivative hDensity hSob hE q hL hσ t u F G hG hNW) A

/-- Different admissible recoveries of this state cannot select different L2 values. -/
theorem recoveredValueL2_unique (v : L2)
    (hv : Lp.toTemperedDistribution v = energyDistribution u) :
    v = recoveredValueL2 hDensity hSob hE q hL hσ t u G := by
  apply FreeFlow.l2_distribution_injective
  rw [hv, recoveredValueL2_distribution hDensity hSob hE q hL hσ t u F G hG hNW]

theorem originalValue_mass_budget_conditional {B CK : ℝ}
    (hB : pureGradientNorm u ≤ B)
    (hTail : tailNorm t G ≤ CK * Real.sqrt L * tailNorm t F) :
    (eLpNorm (energyValue u : V → ℂ) 2 volume).toReal ≤
      B / L + (C0 * CK) * Real.sqrt L * tailNorm t F := by
  rw [← eLpNorm_congr_ae
    (recoveredValueL2_same_value hDensity hSob hE q hL hσ t u F G hG hNW), ← Lp.norm_def]
  exact recoveredValueL2_mass_budget hDensity hSob hE q hL hσ t u F G hB hTail

/-- Main small conditional consumer: a genuine L2 value for the same original
EnergyState, its exact original gradient, and the quantitative mass bound.
The original tested no-waste and actual projected source fields remain inputs. -/
theorem conditional_actual_mass_recovery {B CK : ℝ}
    (hB : pureGradientNorm u ≤ B)
    (hTail : tailNorm t G ≤ CK * Real.sqrt L * tailNorm t F) :
    ∃ v : L2,
      (v : V → ℂ) =ᵐ[volume] energyValue u ∧
      Lp.toTemperedDistribution v = energyDistribution u ∧
      (∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution v) =
        Lp.toTemperedDistribution (energyGradient j u)) ∧
      ‖v‖ ≤ B / L + (C0 * CK) * Real.sqrt L * tailNorm t F := by
  refine ⟨recoveredValueL2 hDensity hSob hE q hL hσ t u G,
    recoveredValueL2_same_value hDensity hSob hE q hL hσ t u F G hG hNW,
    recoveredValueL2_distribution hDensity hSob hE q hL hσ t u F G hG hNW,
    recoveredValueL2_derivative hDensity hSob hE q hL hσ t u F G hG hNW, ?_⟩
  exact recoveredValueL2_mass_budget hDensity hSob hE q hL hσ t u F G hB hTail

end HartreeF.MassRecovery
