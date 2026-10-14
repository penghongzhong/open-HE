import DirectionalStretchGeometry
import L1PaperFourier

/-!
The actual stretched real density b_l(x)=l^((3+alpha)/2)b(T_l x), its L1
domain and its paper-frequency Fourier transform. The inverse transpose is
identified using the produced self-adjoint linear isomorphism and Jacobian.
No Sobolev/weak-gradient pullback or target Fourier scaling is assumed.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace
namespace HartreeF.DirectionalStretch
open GaussianFourierBridge BWork.Gaussian

def stretchedDensity (α : ℝ) (ω : Space) (l : ℝ) (b : Space → ℝ) (x : Space) : ℝ :=
  l^((3+α)/2) * b (stretch ω l x)

theorem density_amplitude_split (α : ℝ) {l : ℝ} (hl : 0 < l) :
    l^((3+α)/2) = l^((1+α)/2) * l := by
  rw [show (3+α)/2 = (1+α)/2+1 by ring, Real.rpow_add hl, Real.rpow_one]

theorem stretchedDensity_nonneg (α : ℝ) (ω : Space) {l : ℝ} (hl : 0 < l)
    {b : Space → ℝ} (hb0 : ∀ x, 0 ≤ b x) (x : Space) :
    0 ≤ stretchedDensity α ω l b x :=
  mul_nonneg (Real.rpow_nonneg hl.le _) (hb0 _)

theorem stretchedDensity_integrable (α : ℝ) {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : 0 < l) {b : Space → ℝ} (hb : Integrable b volume) :
    Integrable (stretchedDensity α ω l b) volume :=
  ((stretch_integrable_iff hω hl b).2 hb).const_mul _

theorem stretchedDensity_integral (α : ℝ) {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : 0 < l) (b : Space → ℝ) :
    (∫ x, stretchedDensity α ω l b x) = l^((1+α)/2) * ∫ x, b x := by
  have hj : l * (∫ x, b (stretch ω l x)) = ∫ x, b x := stretch_integral hω hl b
  unfold stretchedDensity
  rw [integral_const_mul, density_amplitude_split α hl, mul_assoc, hj]

theorem fourierPhase_stretch_transport {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : l ≠ 0) (ξ x : Space) :
    fourierPhase ξ x = fourierPhase (stretch ω l⁻¹ ξ) (stretch ω l x) := by
  unfold fourierPhase
  rw [stretch_self_adjoint, stretch_comp hω, mul_inv_cancel₀ hl, stretch_one]

/-- Total-integral change-of-variables identity. The following domain certificate
supplies the genuine L1 interpretation whenever b is an L1 density. -/
theorem stretchedDensity_fourier (α : ℝ) {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : 0 < l) (b : Space → ℝ) (ξ : Space) :
    paperFourier (stretchedDensity α ω l b) ξ =
      (l^((1+α)/2) : ℝ) * paperFourier b (stretch ω l⁻¹ ξ) := by
  have he : (fun x : Space => fourierPhase ξ x * (stretchedDensity α ω l b x : ℂ)) =
      (fun x => ((l^((3+α)/2) : ℝ) : ℂ) *
        (fourierPhase (stretch ω l⁻¹ ξ) (stretch ω l x) * (b (stretch ω l x) : ℂ))) := by
    funext x
    rw [fourierPhase_stretch_transport hω hl.ne' ξ x]
    unfold stretchedDensity
    push_cast
    ring
  have hj := stretch_integral (F := ℂ) hω hl
    (fun y => fourierPhase (stretch ω l⁻¹ ξ) y * (b y : ℂ))
  change l • (∫ x, fourierPhase (stretch ω l⁻¹ ξ) (stretch ω l x) *
      (b (stretch ω l x) : ℂ)) = paperFourier b (stretch ω l⁻¹ ξ) at hj
  rw [Complex.real_smul] at hj
  change (∫ x, fourierPhase ξ x * (stretchedDensity α ω l b x : ℂ)) = _
  rw [he, integral_const_mul]
  rw [density_amplitude_split α hl, Complex.ofReal_mul, mul_assoc, hj]

/-- The actual L1 density/Fourier producer, with no assumed Jacobian or transform law. -/
theorem stretchedDensity_L1_fourier (α : ℝ) {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : 0 < l) {b : Space → ℝ} (hb : Integrable b volume) :
    Integrable (stretchedDensity α ω l b) volume ∧
    ∀ ξ : Space, paperFourier (stretchedDensity α ω l b) ξ =
      (l^((1+α)/2) : ℝ) * paperFourier b (stretch ω l⁻¹ ξ) :=
  ⟨stretchedDensity_integrable α hω hl hb, stretchedDensity_fourier α hω hl b⟩

#print axioms density_amplitude_split
#print axioms stretchedDensity_nonneg
#print axioms stretchedDensity_integrable
#print axioms stretchedDensity_integral
#print axioms fourierPhase_stretch_transport
#print axioms stretchedDensity_fourier
#print axioms stretchedDensity_L1_fourier
end HartreeF.DirectionalStretch
