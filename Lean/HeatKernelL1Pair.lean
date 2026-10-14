import GaussianL1PairFourier

/-!
The literal normalized heat kernel h_t=(4*pi*t)^(-3/2) exp(-|z|^2/(4t)).
With the paper Fourier convention exp(-i xi dot x), the spectral prefactor is
(2*pi)^(-3), and the Gaussian multiplier is exp(-t|xi|^2). Normalization is
proved algebraically from positive real powers, not assumed as a convention.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.GaussianFourierBridge
open BWork.Gaussian

def heatKernel (t : ℝ) (z : Space) : ℝ :=
  (4*Real.pi*t)^(-(3/2:ℝ)) * Real.exp (-‖z‖^2/(4*t))

def paperInverseFactor : ℝ := ((2*Real.pi)^3)⁻¹

theorem paperInverseFactor_pos : 0 < paperInverseFactor := by
  unfold paperInverseFactor
  positivity

theorem heat_gaussian_normalization {t : ℝ} (ht : 0 < t) :
    (2*Real.pi)^3 * (4*Real.pi*t)^(-(3/2:ℝ)) = (Real.pi/t)^(3/2:ℝ) := by
  have ha : 0 ≤ 2*Real.pi := by positivity
  have hb : 0 ≤ 4*Real.pi*t := by positivity
  have hp : (2*Real.pi)^3 = ((2*Real.pi)^2)^(3/2:ℝ) := by
    rw [← Real.rpow_natCast_mul ha]
    norm_num
  rw [hp, Real.rpow_neg hb, ← div_eq_mul_inv, ← Real.div_rpow (sq_nonneg _) hb]
  congr 1
  field_simp
  ring

theorem heatKernel_eq_gaussianInverse {t : ℝ} (ht : 0 < t) (z : Space) :
    heatKernel t z = paperInverseFactor * gaussianInverseKernel t z := by
  have hn : (2*Real.pi)^3 ≠ 0 := by positivity
  have hc : (4*Real.pi*t)^(-(3/2:ℝ)) =
      paperInverseFactor * (Real.pi/t)^(3/2:ℝ) := by
    rw [paperInverseFactor, ← heat_gaussian_normalization ht, ← mul_assoc,
      inv_mul_cancel₀ hn, one_mul]
  unfold heatKernel gaussianInverseKernel
  rw [hc]
  ring

theorem heatKernel_nonneg {t : ℝ} (ht : 0 < t) (z : Space) : 0 ≤ heatKernel t z := by
  unfold heatKernel
  positivity

/-- Finite actual heat-kernel interaction for signed real L1 input. -/
theorem heat_L1_pair_integrable {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    Integrable (fun q : Space × Space => heatKernel t (q.1-q.2) * f q.1 * f q.2)
      (volume.prod volume) := by
  apply ((gaussian_L1_physical_pair_integrable ht hf).const_mul paperInverseFactor).congr
  filter_upwards [] with q
  rw [heatKernel_eq_gaussianInverse ht]
  ring

/-- Exact fixed-time heat pair/Fourier identity in the paper convention. -/
theorem heat_L1_pair_fourier {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    (∫ q : Space × Space, heatKernel t (q.1-q.2) * f q.1 * f q.2 ∂volume.prod volume) =
      paperInverseFactor * ∫ ξ, Real.exp (-t*‖ξ‖^2) * ‖paperFourier f ξ‖^2 := by
  have he : (fun q : Space × Space => heatKernel t (q.1-q.2) * f q.1 * f q.2) =
      (fun q => paperInverseFactor * (gaussianInverseKernel t (q.1-q.2) * f q.1 * f q.2)) := by
    funext q
    rw [heatKernel_eq_gaussianInverse ht]
    ring
  rw [he, integral_const_mul, gaussian_L1_pair_fourier ht hf]
  rfl

theorem heat_L1_pair_nonneg {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    0 ≤ ∫ q : Space × Space, heatKernel t (q.1-q.2) * f q.1 * f q.2 ∂volume.prod volume := by
  rw [heat_L1_pair_fourier ht hf]
  apply mul_nonneg paperInverseFactor_pos.le
  exact integral_nonneg (fun ξ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))

/-- Domain and identity together: neither side is an unevaluated divergent Bochner integral. -/
theorem heat_L1_pair_domain_and_fourier {t : ℝ} (ht : 0 < t)
    {f : Space → ℝ} (hf : Integrable f volume) :
    Integrable (fun q : Space × Space => heatKernel t (q.1-q.2) * f q.1 * f q.2)
      (volume.prod volume) ∧
    Integrable (fun ξ => Real.exp (-t*‖ξ‖^2) * ‖paperFourier f ξ‖^2) volume ∧
    (∫ q : Space × Space, heatKernel t (q.1-q.2) * f q.1 * f q.2 ∂volume.prod volume) =
      paperInverseFactor * ∫ ξ, Real.exp (-t*‖ξ‖^2) * ‖paperFourier f ξ‖^2 :=
  ⟨heat_L1_pair_integrable ht hf, gaussianFourierEnergy_integrable ht hf,
    heat_L1_pair_fourier ht hf⟩

#print axioms paperInverseFactor_pos
#print axioms heat_gaussian_normalization
#print axioms heatKernel_eq_gaussianInverse
#print axioms heatKernel_nonneg
#print axioms heat_L1_pair_integrable
#print axioms heat_L1_pair_fourier
#print axioms heat_L1_pair_nonneg
#print axioms heat_L1_pair_domain_and_fourier
end HartreeF.GaussianFourierBridge
