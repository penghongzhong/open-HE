import FRieszKernelDerivative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace
namespace HartreeF.RieszConvolutionDerivative
open SobolevStretch

/-- Locally integrable weak gradients of the same actual function are unique a.e. -/
theorem weakGradient_unique {f : Space → ℝ} {G H : Space → Space}
    (hG : HasWeakGradient f G) (hH : HasWeakGradient f H) : G =ᵐ[volume] H := by
  apply ae_eq_of_integral_contDiff_smul_eq hG.gradient_local hH.gradient_local
  intro φ hφ hc
  apply ext_inner_left ℝ
  intro v
  have hiG := hG.gradient_local.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have hiH := hH.gradient_local.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  rw [← integral_inner hiG v, ← integral_inner hiH v]
  have hw := (hG.integration_by_parts v φ hφ hc).symm.trans
    (hH.integration_by_parts v φ hφ hc)
  have he := neg_injective hw
  simpa only [inner_smul_right, real_inner_comm v, mul_comm] using he

#print axioms weakGradient_unique
end HartreeF.RieszConvolutionDerivative
