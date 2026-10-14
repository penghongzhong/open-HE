import ExactBubblePotential
import BubbleWeakLaplacian
import StationaryWeakEquation

/-! Literal positive multiples of the complex Sobolev bubble. The stationary
identity is produced from its actual pointwise convolution and native weak
Laplacian. The sole amplitude condition is an explicit scalar equation. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped RealInnerProductSpace
namespace HartreeF.BubbleProfile
open Bubble SobolevStretch HeatRiesz ForcingDomain StationarySelfTest

def scaledBubble (a : ℝ) (x : Space) : ℂ := a • bubbleC x

def scaledBubbleGradient (a : ℝ) (x : Space) : Space := a • bubbleGradient x

theorem scaledBubble_inDotH1 (a : ℝ) :
    InDotH1 (scaledBubble a) (scaledBubbleGradient a) (fun _ => 0) := by
  have h := bubbleC_inDotH1
  refine ⟨h.function_L6.const_smul a, h.real_gradient_L2.const_smul a, by simp, ?_, ?_⟩
  · refine ⟨?_, (h.real_gradient_L2.const_smul a).locallyIntegrable (by norm_num), ?_⟩
    · simpa [scaledBubble, Complex.real_smul] using
        ((h.function_L6.const_smul a).continuousLinearMap_comp Complex.reCLM).locallyIntegrable
          (by norm_num : (1:ENNReal) ≤ 6)
    · intro v φ hφ hc
      have he := h.real_weak.integration_by_parts v φ hφ hc
      simpa only [scaledBubble, scaledBubbleGradient, Complex.smul_re,
        smul_eq_mul, real_inner_smul_left, mul_assoc, integral_const_mul, mul_neg] using
        congrArg (fun t : ℝ => a*t) he
  · simpa [scaledBubble, bubbleC, Complex.real_smul] using hasWeakGradient_zero

theorem scaledBubble_nonzero_ae {a : ℝ} (ha : 0<a) :
    ¬ scaledBubble a =ᵐ[volume] 0 := by
  intro h
  apply bubbleC_nonzero_ae
  filter_upwards [h] with x hx
  have hz : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  simpa [scaledBubble, Complex.real_smul, hz] using hx

theorem norm_scaledBubble {a : ℝ} (ha : 0≤a) (x : Space) :
    ‖scaledBubble a x‖ = a * bubble x := by
  simp [scaledBubble, Real.norm_of_nonneg ha, norm_bubbleC]

theorem powerDensity_scaledBubble {a : ℝ} (ha : 0≤a) (α : ℝ) (x : Space) :
    powerDensity α (scaledBubble a) x = a^(3+α) * powerDensity α bubbleC x := by
  rw [powerDensity, norm_scaledBubble ha, Real.mul_rpow ha (bubble_pos x).le]
  rw [powerDensity, norm_bubbleC]

theorem potential_scaledBubble {a : ℝ} (ha : 0≤a) (α c : ℝ) (x : Space) :
    potential α c (scaledBubble a) x = a^(3+α) * potential α c bubbleC x := by
  unfold potential
  simp_rw [powerDensity_scaledBubble ha]
  have he (y : Space) : rieszKernel α c (x-y) * (a^(3+α) * powerDensity α bubbleC y) =
      a^(3+α) * (rieszKernel α c (x-y)*powerDensity α bubbleC y) := by ring
  simp_rw [he]
  rw [integral_const_mul]

theorem scaledBubble_forcing_scalar {α a : ℝ} (hα : 0<α) (hα3 : α<3) (ha : 0<a)
    (hamp : bubblePotentialConstant α * a^(4+2*α) = 3) (x : Space) :
    potential α (standardRieszConstant α) (scaledBubble a) x *
        ‖scaledBubble a x‖^(1+α) * (a*bubble x) = 3*a*(bubble x)^5 := by
  rw [potential_scaledBubble ha.le, bubble_potential_power hα hα3,
    norm_scaledBubble ha.le, Real.mul_rpow ha.le (bubble_pos x).le]
  have he : a^(3+α) * (bubblePotentialConstant α * (bubble x)^(3-α)) *
      (a^(1+α)*(bubble x)^(1+α)) * (a*bubble x) =
      (bubblePotentialConstant α * (a^(3+α)*a^(1+α))) * a *
        (((bubble x)^(3-α)*(bubble x)^(1+α))*bubble x) := by ring
  rw [he, ← Real.rpow_add ha, ← Real.rpow_add (bubble_pos x)]
  rw [show (3+α)+(1+α)=4+2*α by ring, show (3-α)+(1+α)=(4:ℝ) by ring, hamp]
  norm_num only [Real.rpow_ofNat]
  ring

theorem scaledBubble_forcing {α a : ℝ} (hα : 0<α) (hα3 : α<3) (ha : 0<a)
    (hamp : bubblePotentialConstant α * a^(4+2*α) = 3) (x : Space) :
    forcing α (standardRieszConstant α) (scaledBubble a) x =
      ((3*a*(bubble x)^5 : ℝ) : ℂ) := by
  have he := scaledBubble_forcing_scalar hα hα3 ha hamp x
  rw [forcing_apply]
  change ((potential α (standardRieszConstant α) (scaledBubble a) x : ℝ) : ℂ) *
      ((‖scaledBubble a x‖^(1+α) : ℝ) : ℂ) * scaledBubble a x = _
  simp only [scaledBubble, bubbleC, Complex.real_smul]
  norm_cast
  simpa only [norm_scaledBubble ha.le, Real.norm_of_nonneg (mul_nonneg ha.le (bubble_pos x).le)] using he

/-- Genuine compact-test stationary equation. No HLS or variational interface
is required to establish this explicit solution. -/
theorem scaledBubble_weakStationary {α a : ℝ} (hα : 0<α) (hα3 : α<3) (ha : 0<a)
    (hamp : bubblePotentialConstant α * a^(4+2*α) = 3) :
    WeakStationary α (standardRieszConstant α) (scaledBubble a)
      (scaledBubbleGradient a) (fun _ => 0) := by
  refine ⟨scaledBubble_inDotH1 a, ?_, ?_⟩
  · intro φ hφ hc
    simp_rw [scaledBubbleGradient, real_inner_smul_left, integral_const_mul,
      bubble_weak_laplacian φ hφ hc, scaledBubble_forcing hα hα3 ha hamp,
      Complex.ofReal_re]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  · intro φ _ _
    simp only [scaledBubble_forcing hα hα3 ha hamp, Complex.ofReal_im,
      inner_zero_left, zero_mul, integral_zero]

theorem scaledBubble_kinetic (a : ℝ) :
    kinetic (scaledBubbleGradient a) (fun _ => 0) = a^2 * (3*Real.pi^2/4) := by
  unfold scaledBubbleGradient
  have hR : MemLp (fun x => a • bubbleGradient x) 2 volume := memLp_bubbleGradient_two.const_smul a
  rw [kinetic_eq_sum hR
    (show MemLp (fun _ : Space => (0:Space)) 2 volume by simp)]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_zero, zero_pow (by decide : (2:ℕ)≠0), integral_zero, add_zero,
    integral_const_mul, bubbleGradient_energy]

#print axioms scaledBubble_inDotH1
#print axioms scaledBubble_nonzero_ae
#print axioms norm_scaledBubble
#print axioms powerDensity_scaledBubble
#print axioms potential_scaledBubble
#print axioms scaledBubble_forcing_scalar
#print axioms scaledBubble_forcing
#print axioms scaledBubble_weakStationary
#print axioms scaledBubble_kinetic
end HartreeF.BubbleProfile
