import FActualHartreeLocalDualSource
import FEnergySchwartzDensity
import Mathlib.Analysis.Calculus.FDeriv.Star

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.LocalDualSource
open EnergySpace LocalChargeBridge

variable {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)

/-- The actual compact smooth conjugate cutoff test, on the original spatial domain. -/
def compactConjugateTest (φ : Test) : Test :=
  (hc.smul_right (f' := fun x => star (φ x))).toSchwartzMap (hχ.smul ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (φ.smooth ⊤)))

@[simp] theorem compactConjugateTest_apply (φ : Test) (x : V) :
    compactConjugateTest hχ hc φ x = χ x • star (φ x) := rfl

theorem compactConjugateTest_compact (φ : Test) :
    HasCompactSupport (compactConjugateTest hχ hc φ : V → ℂ) :=
  hc.smul_right

/-- The derivative is the literal product derivative, with real cutoff coefficients. -/
theorem compactConjugateTest_derivative (φ : Test) (j : Fin 3) (x : V) :
    (∂_{coordinate j} (compactConjugateTest hχ hc φ)) x =
      star (χ x • (∂_{coordinate j} φ) x + coefficientDerivative χ j x • φ x) := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y => χ y • star (φ y)) x (coordinate j) = _
  rw [fderiv_fun_smul (hχ.differentiable (by simp) x) (φ.differentiableAt.star), fderiv_star]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, starL'_apply, star_add, star_smul,
    star_trivial, SchwartzMap.lineDerivOp_apply_eq_fderiv, coefficientDerivative]

/-- The canonical Schwartz state has the original coordinate derivative as representative. -/
theorem schwartzEnergyState_gradient_ae (φ : Test) (j : Fin 3) :
    (energyGradient j (schwartzEnergyState φ) : V → ℂ) =ᵐ[volume]
      (∂_{coordinate j} φ : Test) :=
  (∂_{coordinate j} φ).coeFn_toLp 2 volume

/-- Same-representative derivative identity, without a new weak-gradient input. -/
theorem compactConjugateTest_derivative_ae (φ : Test) (j : Fin 3) :
    (∂_{coordinate j} (compactConjugateTest hχ hc φ) : Test) =ᵐ[volume]
      fun x => star (χ x • energyGradient j (schwartzEnergyState φ) x +
        coefficientDerivative χ j x • energyValue (schwartzEnergyState φ) x) := by
  filter_upwards [schwartzEnergyState_gradient_ae φ j, schwartzEnergyState_value_ae φ] with x hg hv
  rw [compactConjugateTest_derivative hχ hc, hg, hv]

end HartreeF.LocalDualSource
