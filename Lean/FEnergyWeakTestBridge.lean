import FEnergyBanach
import WeakDirectionalStretch
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped RealInnerProductSpace ENNReal SchwartzMap
namespace HartreeF.EnergySpace

/-- The actual homogeneous state satisfies the full complex Schwartz weak
integration-by-parts identity in each coordinate. -/
theorem energyState_schwartz_test (u : EnergyState) (j : Fin 3) (φ : Test) :
    (∫ x, fderiv ℝ φ x (coordinate j) * energyValue u x) =
      -(∫ x, φ x * energyGradient j u x) := by
  have h := congrArg (fun T : TD => T φ) (energyDistribution_derivative u j)
  change (∂_{coordinate j} (Lp.toTemperedDistribution (energyValue u))) φ =
    Lp.toTemperedDistribution (energyGradient j u) φ at h
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, neg_mul,
    integral_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- A compact smooth complex test is an actual Schwartz function, so the
same equality applies to the literal smooth test and its real Frechet derivative. -/
theorem energyState_compact_test (u : EnergyState) (j : Fin 3) (φ : V → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ x, fderiv ℝ φ x (coordinate j) * energyValue u x) =
      -(∫ x, φ x * energyGradient j u x) :=
  energyState_schwartz_test u j (hc.toSchwartzMap hφ)

end HartreeF.EnergySpace
