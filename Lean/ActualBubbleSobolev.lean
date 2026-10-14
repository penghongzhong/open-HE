import ActualBubbleFields
import ClassicalWeakGradient
import DirectionalKineticPositive
import RieszPairIntegrability
import HeatRieszPointwise

/-!
The literal positive bubble lifted to the actual complex homogeneous Sobolev
space, with native compact-test weak gradients, a nonzero a.e class, and the
actual Hartree density profile and finite domains. No bubble-domain or sharp
equality premise is introduced. Optimizer and ground-state claims are separate.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.Bubble
open SobolevStretch HeatRiesz ForcingDomain PressureDomain

def bubbleC (x : Space) : ℂ := (bubble x : ℂ)

theorem norm_bubbleC (x : Space) : ‖bubbleC x‖ = bubble x := by
  rw [bubbleC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (bubble_pos x)]

theorem memLp_bubbleC_six : MemLp bubbleC 6 volume :=
  memLp_bubble_six.continuousLinearMap_comp Complex.ofRealCLM

/-- The classical differential is turned into a genuine weak derivative by
native integration by parts with produced compact-test L1 domains. -/
theorem bubble_hasWeakGradient : HasWeakGradient bubble bubbleGradient :=
  hasWeakGradient_of_differentiable differentiable_bubble continuous_bubbleGradient fderiv_bubble_apply

/-- Actual complex dotH1 membership of Q, with real gradient g and imaginary
zero gradient, is produced without any Sobolev or HLS inequality premise. -/
theorem bubbleC_inDotH1 : InDotH1 bubbleC bubbleGradient (fun _ => 0) := by
  refine ⟨memLp_bubbleC_six, memLp_bubbleGradient_two, by simp, ?_, ?_⟩
  · change HasWeakGradient bubble bubbleGradient
    exact bubble_hasWeakGradient
  · change HasWeakGradient (fun _ : Space => (0:ℝ)) (fun _ => 0)
    exact hasWeakGradient_zero

theorem bubbleC_nonzero_ae : ¬ bubbleC =ᵐ[volume] 0 := by
  intro h
  obtain ⟨x,hx⟩ := h.exists
  have hr := congrArg Complex.re hx
  have hz : bubble x = 0 := by simpa only [bubbleC, Complex.ofReal_re, Pi.zero_apply, Complex.zero_re] using hr
  exact (bubble_pos x).ne' hz

theorem bubbleC_sixthMass_pos : 0 < (∫ x, ‖bubbleC x‖^6) :=
  sixth_mass_pos memLp_bubbleC_six bubbleC_nonzero_ae

/-- The actual Hartree density is the literal primary HLS profile for every
alpha. This pointwise identity alone makes no sharp-equality assertion. -/
theorem powerDensity_bubbleC (α : ℝ) (x : Space) :
    powerDensity α bubbleC x = (1+‖x‖^2)^(-(3+α)/2) := by
  rw [powerDensity, norm_bubbleC, bubble, ← Real.rpow_mul (by positivity : 0 ≤ 1+‖x‖^2)]
  congr 1
  ring

theorem bubbleC_hartree_domains {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) :
    Integrable (rieszPairDensity α (standardRieszConstant α) bubbleC) (volume.prod volume) ∧
    Integrable (fun x => potential α (standardRieszConstant α) bubbleC x *
      powerDensity α bubbleC x) volume := by
  obtain ⟨C,hC⟩ := interaction_density_domain_bound hHLS
  exact ⟨rieszPairDensity_integrable hHLS memLp_bubbleC_six, (hC _ memLp_bubbleC_six).1⟩

#print axioms norm_bubbleC
#print axioms memLp_bubbleC_six
#print axioms bubble_hasWeakGradient
#print axioms bubbleC_inDotH1
#print axioms bubbleC_nonzero_ae
#print axioms bubbleC_sixthMass_pos
#print axioms powerDensity_bubbleC
#print axioms bubbleC_hartree_domains
end HartreeF.Bubble
