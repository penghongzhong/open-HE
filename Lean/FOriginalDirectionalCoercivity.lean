import NormalizedBubbleGroundState

/-!
Acceptance bridge for Theorem 3.3 of the original 64-page v23 manuscript.
The sharp constant is the actual supremum of Hartree/kinetic quotients,
not an unspecified upper bound. The only analytic inputs are the existing
ordinary HLS and sharp HLS/Sobolev interfaces on their full function domains.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
namespace HartreeF.OriginalDirectional
open SobolevStretch HeatRiesz ForcingDomain DirectionalCoercivity SharpOrdinary
open Bubble BubbleProfile

/-- The manuscript's quotient set over all nonzero homogeneous Sobolev classes. -/
def hartreeSobolevQuotients (alpha : ℝ) : Set ℝ :=
  {q | ∃ (f : Space → ℂ) (GRe GIm : Space → Space),
    InDotH1 f GRe GIm ∧ (¬ f =ᵐ[volume] 0) ∧
      q = interaction alpha f / (kinetic GRe GIm)^(3+alpha)}

def originalSharpConstant (alpha : ℝ) : ℝ := sSup (hartreeSobolevQuotients alpha)

/-- Exact identification with the original supremum definition. The lower
bound is supplied by the explicit bubble, not an assumed optimizer. -/
theorem originalSharpConstant_eq_standard {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) :
    originalSharpConstant alpha = standardCombinedConstant alpha := by
  have hbound : ∀ q ∈ hartreeSobolevQuotients alpha,
      q ≤ standardCombinedConstant alpha := by
    rintro q ⟨f, GRe, GIm, hf, hfne, rfl⟩
    have hA : 0 < kinetic GRe GIm := by
      have hm := sixth_mass_pos hf.function_L6 hfne
      have hb := hS.ordinary.bound hf
      by_contra hn
      have hz : kinetic GRe GIm = 0 :=
        le_antisymm (le_of_not_gt hn) (kinetic_nonneg GRe GIm)
      have hzero : (∫ x, ‖f x‖^6) ≤ 0 := by simpa [hz] using hb
      exact (not_lt_of_ge hzero) hm
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hA _)).mpr
    exact exact_combined_hartree_sobolev hOrd hH hS hf
  have hattain : standardCombinedConstant alpha ∈ hartreeSobolevQuotients alpha := by
    refine ⟨bubbleC, bubbleGradient, (fun _ => 0), bubbleC_inDotH1,
      bubbleC_nonzero_ae, ?_⟩
    rw [bubble_combined_equality hH.order_pos hH.order_lt_three]
    exact (mul_div_cancel_right₀ _ (ne_of_gt (Real.rpow_pos_of_pos bubbleC_kinetic_pos _))).symm
  exact le_antisymm (csSup_le ⟨_, hattain⟩ hbound)
    (le_csSup ⟨_, hbound⟩ hattain)

/-- G = C_HS^(-1/(p-1)), written as C_HS^((1-p)^(-1)). -/
def originalKineticThreshold (alpha : ℝ) : ℝ :=
  (originalSharpConstant alpha)^((1-(3+alpha))⁻¹)

theorem originalKineticThreshold_eq_standard {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev) :
    originalKineticThreshold alpha = standardCombinedThreshold alpha := by
  unfold originalKineticThreshold standardCombinedThreshold
  rw [originalSharpConstant_eq_standard hOrd hH hS]

/-- Original Theorem 3.3: the displayed quantitative lower bound and strict
positivity of that very lower bound, for every unit direction. All quantities
are the actual complex homogeneous Sobolev function's physical integrals. -/
theorem original_theorem_3_3 {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    {f : Space → ℂ} {GRe GIm : Space → Space}
    (hf : InDotH1 f GRe GIm) (hfne : ¬ f =ᵐ[volume] 0)
    (hA : 0 < kinetic GRe GIm ∧ kinetic GRe GIm < originalKineticThreshold alpha)
    (hE : energy alpha f GRe GIm < thresholdEnergy alpha (originalKineticThreshold alpha))
    {omega : Space} (homega : ‖omega‖ = 1) :
    0 < (2 * (thresholdEnergy alpha (originalKineticThreshold alpha) -
      energy alpha f GRe GIm) / (originalKineticThreshold alpha - kinetic GRe GIm)) *
      directionalKinetic omega GRe GIm ∧
    (2 * (thresholdEnergy alpha (originalKineticThreshold alpha) -
      energy alpha f GRe GIm) / (originalKineticThreshold alpha - kinetic GRe GIm)) *
      directionalKinetic omega GRe GIm ≤ directionalDefect alpha omega f GRe GIm := by
  rw [originalKineticThreshold_eq_standard hOrd hH hS] at hA hE ⊢
  obtain ⟨hd, hbound, _⟩ :=
    directional_coercivity_at_standard_threshold hOrd hH hS hf hfne homega hA.2
  constructor
  · exact mul_pos (div_pos (mul_pos (by norm_num) (sub_pos.mpr hE))
      (sub_pos.mpr hA.2)) hd
  · convert hbound using 1 <;> ring

#print axioms originalSharpConstant_eq_standard
#print axioms originalKineticThreshold_eq_standard
#print axioms original_theorem_3_3
end HartreeF.OriginalDirectional
