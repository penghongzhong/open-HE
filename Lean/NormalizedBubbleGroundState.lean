import ScaledBubbleStationary
import BubbleSharpCalibration
import ActualGroundStateConsumer

/-! Explicit normalized W on the actual Euclidean complex homogeneous Sobolev
domain. Its weak stationary equation and exact kinetic threshold are produced
without inequality premises. Ordinary inequalities and full H1 density are used
only to compare its energy with all weak stationary states. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.BubbleProfile
open Bubble SobolevStretch HeatRiesz ForcingDomain SharpOrdinary DirectionalCoercivity
open StationarySelfTest

def normalizedBubble (α : ℝ) : Space → ℂ := scaledBubble (bubbleAmplitude α)
def normalizedBubbleGradient (α : ℝ) : Space → Space := scaledBubbleGradient (bubbleAmplitude α)

theorem normalizedBubble_inDotH1 (α : ℝ) :
    InDotH1 (normalizedBubble α) (normalizedBubbleGradient α) (fun _ => 0) :=
  scaledBubble_inDotH1 _

theorem normalizedBubble_nonzero_ae {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    ¬ normalizedBubble α =ᵐ[volume] 0 :=
  scaledBubble_nonzero_ae (bubbleAmplitude_pos hα hα3)

/-- This explicit W solves the actual weak Hartree equation, without assuming
HLS, a Sobolev inequality, a ground state, or any target stationary identity. -/
theorem normalizedBubble_weakStationary {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    WeakStationary α (standardRieszConstant α) (normalizedBubble α)
      (normalizedBubbleGradient α) (fun _ => 0) :=
  scaledBubble_weakStationary hα hα3 (bubbleAmplitude_pos hα hα3)
    (bubbleAmplitude_balance hα hα3)

theorem normalizedBubble_kinetic_eq_threshold {α : ℝ} (hα : 0<α) (hα3 : α<3) :
    kinetic (normalizedBubbleGradient α) (fun _ => 0) = standardCombinedThreshold α := by
  rw [normalizedBubbleGradient, scaledBubble_kinetic]
  exact bubbleAmplitude_kinetic_eq_threshold hα hα3

/-- Native attainment proves that every universal combined Hartree-Sobolev
coefficient is at least the explicit product constant. -/
theorem combinedConstant_optimal {α C : ℝ} (hα : 0<α) (hα3 : α<3)
    (hC : ∀ (u : Space → ℂ) (GRe GIm : Space → Space), InDotH1 u GRe GIm →
      interaction α u ≤ C * (kinetic GRe GIm)^(3+α)) :
    standardCombinedConstant α ≤ C := by
  have h := hC bubbleC bubbleGradient (fun _ => 0) bubbleC_inDotH1
  rw [bubble_combined_equality hα hα3] at h
  have hp := Real.rpow_pos_of_pos bubbleC_kinetic_pos (3+α)
  nlinarith

/-- The explicit W is a genuine least-energy nonzero weak stationary state.
The all-function sharp inequalities and ordinary H1 density remain visible. -/
theorem normalizedBubble_isGroundState {α : ℝ}
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density) :
    IsGroundState α (normalizedBubble α) (normalizedBubbleGradient α) (fun _ => 0) :=
  IsGroundState.of_stationary_and_threshold_kinetic
    (normalizedBubble_weakStationary hH.order_pos hH.order_lt_three) hOrd hH hS hDensity
    (normalizedBubble_nonzero_ae hH.order_pos hH.order_lt_three)
    (normalizedBubble_kinetic_eq_threshold hH.order_pos hH.order_lt_three)

theorem groundState_kinetic_eq_standard {α : ℝ} {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : IsGroundState α u GRe GIm)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density) :
    kinetic GRe GIm = standardCombinedThreshold α :=
  h.kinetic_eq_of_threshold_state
    (normalizedBubble_weakStationary hH.order_pos hH.order_lt_three)
    (normalizedBubble_nonzero_ae hH.order_pos hH.order_lt_three)
    (normalizedBubble_kinetic_eq_threshold hH.order_pos hH.order_lt_three) hOrd hH hS hDensity

theorem groundState_energy_eq_standard {α : ℝ} {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : IsGroundState α u GRe GIm)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density) :
    energy α u GRe GIm = thresholdEnergy α (standardCombinedThreshold α) :=
  h.energy_eq_of_threshold_state
    (normalizedBubble_weakStationary hH.order_pos hH.order_lt_three)
    (normalizedBubble_nonzero_ae hH.order_pos hH.order_lt_three)
    (normalizedBubble_kinetic_eq_threshold hH.order_pos hH.order_lt_three) hOrd hH hS hDensity

/-- Physical directional coercivity below any actual ground state. The
threshold-attaining witness is now the constructed W, not an input. -/
theorem directional_coercivity_below_groundState {α : ℝ} {u f : Space → ℂ}
    {GRe GIm FRe FIm : Space → Space} (h : IsGroundState α u GRe GIm)
    (hOrd : OrdinaryHLS α (standardRieszConstant α))
    (hH : SharpOrdinaryHLS α) (hS : SharpOrdinarySobolev) (hDensity : OrdinaryH1Density)
    (hf : InDotH1 f FRe FIm) (hfne : ¬ f =ᵐ[volume] 0) {ω : Space} (hω : ‖ω‖ = 1)
    (hgap : kinetic FRe FIm < kinetic GRe GIm) :
    0 < directionalKinetic ω FRe FIm ∧
    2*(energy α u GRe GIm-energy α f FRe FIm)*directionalKinetic ω FRe FIm /
      (kinetic GRe GIm-kinetic FRe FIm) ≤ directionalDefect α ω f FRe FIm ∧
    (energy α f FRe FIm < energy α u GRe GIm →
      0 < directionalDefect α ω f FRe FIm) :=
  h.directional_coercivity_below
    (normalizedBubble_weakStationary hH.order_pos hH.order_lt_three)
    (normalizedBubble_nonzero_ae hH.order_pos hH.order_lt_three)
    (normalizedBubble_kinetic_eq_threshold hH.order_pos hH.order_lt_three)
    hOrd hH hS hDensity hf hfne hω hgap

#print axioms normalizedBubble_inDotH1
#print axioms normalizedBubble_nonzero_ae
#print axioms normalizedBubble_weakStationary
#print axioms normalizedBubble_kinetic_eq_threshold
#print axioms combinedConstant_optimal
#print axioms normalizedBubble_isGroundState
#print axioms groundState_kinetic_eq_standard
#print axioms groundState_energy_eq_standard
#print axioms directional_coercivity_below_groundState
end HartreeF.BubbleProfile
