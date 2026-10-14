import DirectionalPairChange
import ActualRieszFourierBridge
import FourierStretchKernel

/-!
Actual spectral Phi representation of the physical directional stretch energy.
It is produced by applying the proved Riesz/Fourier bridge to the actual
stretched L1 density, then applying the proved frequency Jacobian. Spectral
integrability is produced before any integral is rewritten. No representation,
convexity, or spectral derivative is an input hypothesis.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.PhysicalSpectral
open PhysicalStretch DirectionalStretch HeatRiesz GaussianFourierBridge BWork.Gaussian

def spectralStretchPair (α : ℝ) (ω : Space) (b : Space → ℝ) (s : ℝ) (ξ : Space) : ℝ :=
  stretchKernel (α/2) (longitudinalSq ω ξ) (transverseSq ω ξ) s * ‖paperFourier b ξ‖^2

theorem fourier_amplitude_square (α : ℝ) {l : ℝ} (hl : 0 < l) :
    (l^((1+α)/2))^2 = l^(1+α) := by
  rw [← Real.rpow_mul_natCast hl.le]
  congr 1
  push_cast
  ring

theorem spectralStretchPair_pullback (α : ℝ) {ω : Space} (hω : ‖ω‖ = 1)
    {l : ℝ} (hl : 0 < l) (b : Space → ℝ) (ξ : Space) :
    spectralStretchPair α ω b (l^2) ξ =
      l * (‖stretch ω l ξ‖^(-α) *
        ‖paperFourier (stretchedDensity α ω l b) (stretch ω l ξ)‖^2) := by
  rw [stretchedDensity_fourier α hω hl, stretch_inverse hω hl.ne']
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hl ((1+α)/2)), mul_pow]
  rw [fourier_amplitude_square α hl]
  have hs : (l^2)^(1+α/2) = l*l^(1+α) := by
    calc
      _ = l^(2+α) := by
        rw [← Real.rpow_natCast_mul hl.le]
        congr 1
        push_cast
        ring
      _ = l^(1:ℝ) * l^(1+α) := by
        rw [← Real.rpow_add hl]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  have hn : (longitudinalSq ω ξ*l^2+transverseSq ω ξ)^(-(α/2)) =
      ‖stretch ω l ξ‖^(-α) := by
    rw [show longitudinalSq ω ξ*l^2+transverseSq ω ξ = ‖stretch ω l ξ‖^2 by
      rw [stretch_norm_sq hω]; ring,
      ← Real.rpow_natCast_mul (norm_nonneg (stretch ω l ξ))]
    congr 1
    push_cast
    ring
  unfold spectralStretchPair stretchKernel
  rw [hs, hn]
  ring

/-- Actual frequency domain and physical/spectral identity at the genuine l^2 scale. -/
theorem physicalStretch_spectral_square {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {ω : Space} (hω : ‖ω‖ = 1) {l : ℝ} (hl : 0 < l)
    {b : Space → ℝ} (hb : Integrable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    Integrable (spectralStretchPair α ω b (l^2)) volume ∧
    physicalStretchEnergy α (standardRieszConstant α) ω b (l^2) =
      paperInverseFactor * ∫ ξ, spectralStretchPair α ω b (l^2) ξ := by
  have hd := stretchedDensity_riesz_domain_and_energy hα3
    (standardRieszConstant_pos hα hα3).le hω hl hb.aestronglyMeasurable hb0 hpair
  have hL := stretchedDensity_integrable α hω hl hb
  have h0 := stretchedDensity_nonneg α ω hl hb0
  obtain ⟨hS, he⟩ := standardRiesz_L1_domain_and_fourier hα hα3 hL h0 hd.1
  let g : Space → ℝ := fun ξ => ‖ξ‖^(-α) *
    ‖paperFourier (stretchedDensity α ω l b) ξ‖^2
  have hSp : Integrable g volume := hS
  have hp := (stretch_integrable_iff hω hl g).2 hSp
  have hf : (fun ξ => l*g (stretch ω l ξ)) = spectralStretchPair α ω b (l^2) := by
    funext ξ
    exact (spectralStretchPair_pullback α hω hl b ξ).symm
  have hint : Integrable (spectralStretchPair α ω b (l^2)) volume := by
    rw [← hf]
    exact hp.const_mul l
  refine ⟨hint, ?_⟩
  have hj : l * (∫ ξ, g (stretch ω l ξ)) = ∫ ξ, g ξ := stretch_integral hω hl g
  have hspec : (∫ ξ, spectralStretchPair α ω b (l^2) ξ) = ∫ ξ, g ξ := by
    rw [← hf, integral_const_mul, hj]
  calc
    _ = ∫ q, standardRieszPair α (stretchedDensity α ω l b) q ∂volume.prod volume := hd.2.symm
    _ = paperInverseFactor * ∫ ξ, g ξ := he
    _ = _ := by rw [hspec]

/-- Every positive s is realized by the actual l=sqrt(s) stretch. -/
theorem physicalStretch_spectral_domain_and_identity {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s)
    {b : Space → ℝ} (hb : Integrable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    Integrable (spectralStretchPair α ω b s) volume ∧
    physicalStretchEnergy α (standardRieszConstant α) ω b s =
      paperInverseFactor * ∫ ξ, spectralStretchPair α ω b s ξ := by
  simpa only [Real.sq_sqrt hs.le] using
    physicalStretch_spectral_square hα hα3 hω (Real.sqrt_pos.mpr hs) hb hb0 hpair

#print axioms fourier_amplitude_square
#print axioms spectralStretchPair_pullback
#print axioms physicalStretch_spectral_square
#print axioms physicalStretch_spectral_domain_and_identity
end HartreeF.PhysicalSpectral
