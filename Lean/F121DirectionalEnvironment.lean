import F121DirectionalSobolev
import FOriginalDirectionalCoercivity
import FStateSharpGroundThreshold

/-! R8.4 Lemma 7.4, pages 58--59, both conclusions (45) and (46).
The sharp threshold is the original supremum and the energy level is that of
the explicit normalized weak ground state W. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
namespace HartreeF.Paper121Directional
open SobolevStretch ForcingDomain HeatRiesz SharpOrdinary DirectionalCoercivity
  OriginalDirectional StateEnergy StateSharpThreshold StationarySelfTest

theorem directional_coercivity_original_environment {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (hDensity : OrdinaryH1Density)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm)
    (hne : ¬ u =ᵐ[volume] 0)
    (hA : kinetic GRe GIm < originalKineticThreshold alpha)
    (hE : energy alpha u GRe GIm < totalEnergy alpha (normalizedBubbleState alpha))
    {omega : Space} (homega : ‖omega‖ = 1) :
    0 < (2 * (totalEnergy alpha (normalizedBubbleState alpha) -
      energy alpha u GRe GIm) / (originalKineticThreshold alpha - kinetic GRe GIm)) *
      directionalKinetic omega GRe GIm ∧
    (2 * (totalEnergy alpha (normalizedBubbleState alpha) -
      energy alpha u GRe GIm) / (originalKineticThreshold alpha - kinetic GRe GIm)) *
      directionalKinetic omega GRe GIm ≤ directionalDefect alpha omega u GRe GIm ∧
    (∫ x, ‖u x‖ ^ 6) ≤
      8 * sharpSobolevSixth * (kinetic GRe GIm) ^ 2 * directionalKinetic omega GRe GIm := by
  have hEw : totalEnergy alpha (normalizedBubbleState alpha) =
      thresholdEnergy alpha (originalKineticThreshold alpha) := by
    rw [originalKineticThreshold_eq_standard hOrd hH hS]
    exact normalizedBubbleState_energy hOrd hH hS hDensity
  have hpositive : 0 < kinetic GRe GIm := by
    have hm := sixth_mass_pos hu.function_L6 hne
    have hb := hS.ordinary.bound hu
    by_contra hn
    have hz : kinetic GRe GIm = 0 :=
      le_antisymm (le_of_not_gt hn) (kinetic_nonneg GRe GIm)
    rw [hz] at hb
    norm_num only [zero_pow, mul_zero] at hb
    exact (not_lt_of_ge hb) hm
  have hc := original_theorem_3_3 hOrd hH hS hu hne ⟨hpositive, hA⟩
    (hEw ▸ hE) homega
  rw [← hEw] at hc
  exact ⟨hc.1, hc.2, directional_sixth_bound hS.ordinary hu hne homega⟩

end HartreeF.Paper121Directional
