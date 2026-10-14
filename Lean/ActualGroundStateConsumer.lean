import StationaryGroundLowerBound

/-!
Actual least-energy stationary states for the standard Riesz normalization.
The explicit threshold-attaining stationary state remains a displayed witness
input until the independent bubble construction supplies it. No existence or
attainment conclusion is silently assumed inside the ground-state definition.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.StationarySelfTest
open SobolevStretch ForcingDomain HeatRiesz SharpOrdinary DirectionalCoercivity

/-- A genuine nonzero weak stationary state minimizing the actual energy over
all genuine nonzero weak stationary states with the same standard kernel. -/
structure IsGroundState (α : ℝ) (u : Space → ℂ)
    (GRe GIm : Space → Space) : Prop where
  stationary : WeakStationary α (standardRieszConstant α) u GRe GIm
  nonzero : ¬ u =ᵐ[volume] 0
  minimal : ∀ (v : Space → ℂ) (HRe HIm : Space → Space),
    WeakStationary α (standardRieszConstant α) v HRe HIm →
    (¬ v =ᵐ[volume] 0) → energy α u GRe GIm ≤ energy α v HRe HIm

/-- A real stationary threshold achiever is a ground state by the produced
universal stationary lower bound. Attainment is explicit in this consumer. -/
theorem IsGroundState.of_stationary_and_threshold_energy {α : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space}
    (h : WeakStationary α (standardRieszConstant α) u GRe GIm)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev)
    (hDensity : OrdinaryH1Density) (hnonzero : ¬ u =ᵐ[volume] 0)
    (hE : energy α u GRe GIm = thresholdEnergy α (standardCombinedThreshold α)) :
    IsGroundState α u GRe GIm := by
  refine ⟨h, hnonzero, ?_⟩
  intro v HRe HIm hv hvnonzero
  rw [hE]
  exact hv.energy_ge_standard_threshold hOrd hH hS hDensity hvnonzero

/-- The native stationary energy identity converts kinetic attainment into
energy attainment, so the actual W construction need only compute A(W). -/
theorem IsGroundState.of_stationary_and_threshold_kinetic {α : ℝ} {u : Space → ℂ}
    {GRe GIm : Space → Space}
    (h : WeakStationary α (standardRieszConstant α) u GRe GIm)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev)
    (hDensity : OrdinaryH1Density) (hnonzero : ¬ u =ᵐ[volume] 0)
    (hA : kinetic GRe GIm = standardCombinedThreshold α) :
    IsGroundState α u GRe GIm := by
  apply IsGroundState.of_stationary_and_threshold_energy h hOrd hH hS hDensity hnonzero
  rw [h.energy_eq_thresholdEnergy hOrd hDensity hS.ordinary, hA]

/-- With one genuine threshold-attaining witness, every actual ground state
has the same threshold energy. The witness is not part of IsGroundState. -/
theorem IsGroundState.energy_eq_of_threshold_state {α : ℝ} {u w : Space → ℂ}
    {GRe GIm WRe WIm : Space → Space} (h : IsGroundState α u GRe GIm)
    (hw : WeakStationary α (standardRieszConstant α) w WRe WIm)
    (hwne : ¬ w =ᵐ[volume] 0)
    (hwA : kinetic WRe WIm = standardCombinedThreshold α)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev)
    (hDensity : OrdinaryH1Density) :
    energy α u GRe GIm = thresholdEnergy α (standardCombinedThreshold α) := by
  apply le_antisymm
  · have hmin := h.minimal w WRe WIm hw hwne
    rwa [hw.energy_eq_thresholdEnergy hOrd hDensity hS.ordinary, hwA] at hmin
  · exact h.stationary.energy_ge_standard_threshold hOrd hH hS hDensity h.nonzero

/-- Ground-state kinetic calibration is a conclusion from minimization,
stationary self-testing, and the explicit actual threshold witness. -/
theorem IsGroundState.kinetic_eq_of_threshold_state {α : ℝ} {u w : Space → ℂ}
    {GRe GIm WRe WIm : Space → Space} (h : IsGroundState α u GRe GIm)
    (hw : WeakStationary α (standardRieszConstant α) w WRe WIm)
    (hwne : ¬ w =ᵐ[volume] 0)
    (hwA : kinetic WRe WIm = standardCombinedThreshold α)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev)
    (hDensity : OrdinaryH1Density) :
    kinetic GRe GIm = standardCombinedThreshold α := by
  have he := h.energy_eq_of_threshold_state hw hwne hwA hOrd hH hS hDensity
  rw [h.stationary.energy_eq_thresholdEnergy hOrd hDensity hS.ordinary] at he
  unfold thresholdEnergy at he
  have hc : (2+α)/(2*(3+α)) ≠ 0 := ne_of_gt
    (div_pos (by linarith [hH.order_pos]) (by linarith [hH.order_pos]))
  exact mul_left_cancel₀ hc he

/-- The existing physical DC producer now uses an actual ground-state kinetic
threshold, once the displayed stationary witness has been constructed. -/
theorem IsGroundState.directional_coercivity_below {α : ℝ} {u w f : Space → ℂ}
    {GRe GIm WRe WIm FRe FIm : Space → Space} (h : IsGroundState α u GRe GIm)
    (hw : WeakStationary α (standardRieszConstant α) w WRe WIm)
    (hwne : ¬ w =ᵐ[volume] 0)
    (hwA : kinetic WRe WIm = standardCombinedThreshold α)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev)
    (hDensity : OrdinaryH1Density) (hf : InDotH1 f FRe FIm)
    (hfne : ¬ f =ᵐ[volume] 0) {ω : Space} (hω : ‖ω‖ = 1)
    (hgap : kinetic FRe FIm < kinetic GRe GIm) :
    0 < directionalKinetic ω FRe FIm ∧
    2*(energy α u GRe GIm-energy α f FRe FIm)*directionalKinetic ω FRe FIm /
      (kinetic GRe GIm-kinetic FRe FIm) ≤ directionalDefect α ω f FRe FIm ∧
    (energy α f FRe FIm < energy α u GRe GIm →
      0 < directionalDefect α ω f FRe FIm) := by
  have hA := h.kinetic_eq_of_threshold_state hw hwne hwA hOrd hH hS hDensity
  have hE := h.energy_eq_of_threshold_state hw hwne hwA hOrd hH hS hDensity
  rw [hA] at hgap
  rw [hA, hE]
  exact directional_coercivity_at_standard_threshold hOrd hH hS hf hfne hω hgap

#print axioms IsGroundState
#print axioms IsGroundState.of_stationary_and_threshold_energy
#print axioms IsGroundState.of_stationary_and_threshold_kinetic
#print axioms IsGroundState.energy_eq_of_threshold_state
#print axioms IsGroundState.kinetic_eq_of_threshold_state
#print axioms IsGroundState.directional_coercivity_below
end HartreeF.StationarySelfTest
