import FRieszConvolutionWeakDerivative

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.RieszConvolutionDerivative
open ForcingDomain RieszWeakDerivative RieszKernelDerivative SobolevStretch GradientMajorants

/-- The exact upper-alpha exponents and coefficient for arbitrary real density. -/
theorem rieszConvolution_derivative_endpoint {α c c' : ℝ}
    (hH : OrdinaryHLS α c) (hL : OrdinaryHLS (α-1) c') :
    ∃ C : ℝ≥0, ∀ f : Space → ℝ,
      MemLp f (ENNReal.ofReal (6/(3+α))) volume →
      (∀ᵐ x ∂volume, Integrable (fun y => f y • rieszKernelGradient α c (x-y)) volume) ∧
      MemLp (gradientConvolution α c f) (ENNReal.ofReal (6/(5-α))) volume ∧
      eLpNorm (gradientConvolution α c f) (ENNReal.ofReal (6/(5-α))) volume ≤
        (ENNReal.ofReal (c * (3-α) / c') * C) *
          eLpNorm f (ENNReal.ofReal (6/(3+α))) volume ∧
      HasWeakGradient (rieszConvolution α c f) (gradientConvolution α c f) := by
  have hs : α/3 < (3+α)/6 := by linarith [hH.order_lt_three]
  have hs1 : (3+α)/6 < 1 := by linarith [hH.order_lt_three]
  have hsL : (α-1)/3 < (3+α)/6 := by linarith [hH.order_lt_three]
  have heqin : 1/((3+α)/6) = 6/(3+α) := by simp
  have heqout : 1/((3+α)/6-(α-1)/3) = 6/(5-α) := by
    rw [show (3+α)/6-(α-1)/3 = (5-α)/6 by ring]
    simp
  obtain ⟨hp,hpα,hq,hrel⟩ := reciprocal_hls_range hL.order_pos hsL hs1
  rw [heqin] at hp hpα hrel
  rw [heqout] at hq hrel
  obtain ⟨C,hC⟩ := gradientConvolution_bound hH.order_lt_three hH.normalization_pos hL
    hp hpα hq hrel
  refine ⟨C,?_⟩
  intro f hf
  have h := hC f hf
  refine ⟨h.1,h.2.1,h.2.2,?_⟩
  apply rieszConvolution_hasWeakGradient hH hL hs hs1
  simpa only [heqin] using hf

#print axioms rieszConvolution_derivative_endpoint
end HartreeF.RieszConvolutionDerivative
