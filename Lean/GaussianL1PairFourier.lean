import L1PaperFourier

/-!
The actual fixed-Gaussian pair/Fourier identity on real L1 data, proved from
an absolutely integrable three-variable complex integrand and genuine Fubini.
The Fourier convention is the paper convention exp(-i xi dot x). No L2,
Plancherel, Riesz/Fourier bridge, or target pair identity is a premise.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate
namespace HartreeF.GaussianFourierBridge
open BWork.Gaussian

def gaussianInverseKernel (t : ℝ) (z : Space) : ℝ :=
  (Real.pi/t)^(3/2:ℝ) * Real.exp (-‖z‖^2/(4*t))

def gaussianFourierTriple (t : ℝ) (f : Space → ℝ) (p : Space × (Space × Space)) : ℂ :=
  (gaussianRate t p.1 : ℂ) * fourierPhase p.1 (p.2.1-p.2.2) *
    (f p.2.1 : ℂ) * (f p.2.2 : ℂ)

theorem gaussianInverseKernel_eq_integral {t : ℝ} (ht : 0 < t) (z : Space) :
    (gaussianInverseKernel t z : ℂ) =
      ∫ ξ, (gaussianRate t ξ : ℂ) * fourierPhase ξ z := by
  have h := gaussianRate_fourier ht z
  change (∫ ξ, fourierPhase z ξ * (gaussianRate t ξ : ℂ)) = _ at h
  rw [show (fun ξ => (gaussianRate t ξ : ℂ) * fourierPhase ξ z) =
      (fun ξ => fourierPhase z ξ * (gaussianRate t ξ : ℂ)) by
        funext ξ; rw [fourierPhase_symm ξ z, mul_comm]]
  rw [h]
  simp only [gaussianInverseKernel, Complex.ofReal_mul]

theorem gaussianFourierTriple_aestronglyMeasurable (t : ℝ)
    {f : Space → ℝ} (hf : Integrable f volume) :
    AEStronglyMeasurable (gaussianFourierTriple t f) (volume.prod (volume.prod volume)) := by
  have hg : Continuous (fun p : Space × (Space × Space) => (gaussianRate t p.1 : ℂ)) :=
    Complex.continuous_ofReal.comp ((gaussianRate_continuous t).comp continuous_fst)
  have hp : Continuous (fun p : Space × (Space × Space) => fourierPhase p.1 (p.2.1-p.2.2)) :=
    fourierPhase_continuous.comp (continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))
  exact ((hg.aestronglyMeasurable.mul hp.aestronglyMeasurable).mul
    hf.ofReal.aestronglyMeasurable.comp_fst.comp_snd).mul
      hf.ofReal.aestronglyMeasurable.comp_snd.comp_snd

/-- Absolute triple Fubini domain, with majorant g_t(xi)|f(x)||f(y)|. -/
theorem gaussianFourierTriple_integrable {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    Integrable (gaussianFourierTriple t f) (volume.prod (volume.prod volume)) := by
  have hdom := (gaussianRate_real_integrable ht).mul_prod (hf.norm.mul_prod hf.norm)
  apply hdom.mono' (gaussianFourierTriple_aestronglyMeasurable t hf)
  filter_upwards [] with p
  simp only [gaussianFourierTriple, norm_mul, norm_fourierPhase, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (gaussianRate_nonneg t p.1), mul_one]
  exact le_of_eq (by ring)

/-- Fourier factorization of the actual physical pair integral at fixed frequency. -/
theorem gaussianFourierTriple_physical_integral (t : ℝ) (f : Space → ℝ) (ξ : Space) :
    (∫ q : Space × Space, gaussianFourierTriple t f (ξ,q) ∂volume.prod volume) =
      (gaussianRate t ξ : ℂ) * (paperFourier f ξ * conj (paperFourier f ξ)) := by
  have he : (fun q : Space × Space => gaussianFourierTriple t f (ξ,q)) =
      (fun q => (gaussianRate t ξ : ℂ) *
        ((fourierPhase ξ q.1 * (f q.1 : ℂ)) *
          (fourierPhase (-ξ) q.2 * (f q.2 : ℂ)))) := by
    funext q
    unfold gaussianFourierTriple
    rw [fourierPhase_sub]
    ring
  have hp := integral_prod_mul (μ := volume) (ν := volume) (fun x : Space => fourierPhase ξ x * (f x : ℂ))
    (fun y : Space => fourierPhase (-ξ) y * (f y : ℂ))
  rw [he, integral_const_mul, hp]
  change (gaussianRate t ξ : ℂ) * (paperFourier f ξ * paperFourier f (-ξ)) = _
  rw [paperFourier_neg]

/-- Gaussian inversion is used only for a genuine integrable Gaussian, pointwise in x-y. -/
theorem gaussianFourierTriple_spectral_integral {t : ℝ} (ht : 0 < t)
    (f : Space → ℝ) (q : Space × Space) :
    (∫ ξ, gaussianFourierTriple t f (ξ,q)) =
      (gaussianInverseKernel t (q.1-q.2) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ) := by
  unfold gaussianFourierTriple
  dsimp only
  rw [integral_mul_const, integral_mul_const, ← gaussianInverseKernel_eq_integral ht]

/-- The complex-valued pair identity follows by Fubini from proved absolute triple integrability. -/
theorem gaussian_L1_pair_fourier_complex {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    (∫ q : Space × Space, (gaussianInverseKernel t (q.1-q.2) : ℂ) *
      (f q.1 : ℂ) * (f q.2 : ℂ) ∂volume.prod volume) =
    ∫ ξ, (gaussianRate t ξ : ℂ) * (paperFourier f ξ * conj (paperFourier f ξ)) := by
  have hT := gaussianFourierTriple_integrable ht hf
  calc
    _ = ∫ q : Space × Space, (∫ ξ : Space, gaussianFourierTriple t f (ξ,q)) ∂volume.prod volume := by
      exact integral_congr_ae (Filter.Eventually.of_forall (fun q =>
        (gaussianFourierTriple_spectral_integral ht f q).symm))
    _ = ∫ p : Space × (Space × Space), gaussianFourierTriple t f p
        ∂volume.prod (volume.prod volume) := (integral_prod_symm _ hT).symm
    _ = ∫ ξ, ∫ q : Space × Space, gaussianFourierTriple t f (ξ,q)
        ∂volume.prod volume := integral_prod _ hT
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall
      (gaussianFourierTriple_physical_integral t f))

/-- Actual physical Gaussian pair absolute integrability, including signed real L1 data. -/
theorem gaussian_L1_physical_pair_integrable {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    Integrable (fun q : Space × Space => gaussianInverseKernel t (q.1-q.2) * f q.1 * f q.2)
      (volume.prod volume) := by
  have h := (gaussianFourierTriple_integrable ht hf).integral_prod_right
  have hc : Integrable (fun q : Space × Space =>
      (gaussianInverseKernel t (q.1-q.2) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ))
      (volume.prod volume) := by
    apply h.congr
    exact Filter.Eventually.of_forall (gaussianFourierTriple_spectral_integral ht f)
  have hcast : Integrable (fun q : Space × Space =>
      ((gaussianInverseKernel t (q.1-q.2) * f q.1 * f q.2 : ℝ) : ℂ))
      (volume.prod volume) := by
    apply hc.congr
    filter_upwards [] with q
    push_cast
    rfl
  exact hcast.re

/-- The real fixed-Gaussian pair identity. Both sides have separately proved finite domains. -/
theorem gaussian_L1_pair_fourier {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    (∫ q : Space × Space, gaussianInverseKernel t (q.1-q.2) * f q.1 * f q.2
      ∂volume.prod volume) = ∫ ξ, gaussianRate t ξ * ‖paperFourier f ξ‖^2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  have h := gaussian_L1_pair_fourier_complex ht hf
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with q
    push_cast
    rfl
  · apply integral_congr_ae
    filter_upwards [] with ξ
    rw [Complex.mul_conj']
    push_cast
    rfl

#print axioms gaussianInverseKernel_eq_integral
#print axioms gaussianFourierTriple_aestronglyMeasurable
#print axioms gaussianFourierTriple_integrable
#print axioms gaussianFourierTriple_physical_integral
#print axioms gaussianFourierTriple_spectral_integral
#print axioms gaussian_L1_pair_fourier_complex
#print axioms gaussian_L1_physical_pair_integrable
#print axioms gaussian_L1_pair_fourier
end HartreeF.GaussianFourierBridge
