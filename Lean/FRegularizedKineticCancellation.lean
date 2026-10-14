import FEnergyRegularizerDerivatives

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace HartreeF.Regularization
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest

theorem l2_real_inner_eq_re (f g : EnergySpace.L2) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, (inner ℂ (f x) (g x)).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact real_inner_eq_re_inner ℂ (f x) (g x)
    _ = _ := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)

theorem BoundedSymbol.l2_commute (m q : BoundedSymbol) (f : EnergySpace.L2) :
    m.l2 (q.l2 f) = q.l2 (m.l2 f) := by
  apply FreeFlow.l2_distribution_injective
  simp_rw [BoundedSymbol.l2_distribution]
  exact m.distribution_commute q _

theorem BoundedSymbol.real_inner_I_cross_eq_zero (m q : BoundedSymbol)
    (hm : ∀ ξ, star (m.symbol ξ) = m.symbol ξ)
    (hq : ∀ ξ, star (q.symbol ξ) = q.symbol ξ) (f : EnergySpace.L2) :
    inner ℝ (m.l2 f) (Complex.I • q.l2 f) = 0 := by
  have hs : inner ℂ (m.l2 f) (q.l2 f) = inner ℂ (q.l2 f) (m.l2 f) := by
    calc
      _ = inner ℂ f (m.l2 (q.l2 f)) := m.l2_selfAdjoint hm f _
      _ = inner ℂ f (q.l2 (m.l2 f)) := congrArg (inner ℂ f) (m.l2_commute q f)
      _ = _ := (q.l2_selfAdjoint hq f _).symm
  have hc : star (inner ℂ (m.l2 f) (q.l2 f)) = inner ℂ (m.l2 f) (q.l2 f) :=
    (inner_conj_symm _ _).trans hs.symm
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hi
  rw [l2_real_inner_eq_re, inner_smul_right]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  linarith

namespace Actual

theorem laplaceSymbol_real (n : ℕ) (ξ : V) :
    star ((laplaceCutoff n).symbol ξ) = (laplaceCutoff n).symbol ξ := by
  simp only [laplaceCutoff, laplaceSymbol, Pi.smul_apply, smul_eq_mul,
    Pi.mul_apply, star_mul, star_neg, star_pow, star_symbol, normSqSymbol]
  simp
  ring

/-- The actual kinetic/Laplacian skew term vanishes in every gradient
coordinate. The proof uses the literal real commuting Fourier multipliers. -/
theorem regularized_kinetic_laplacian_zero (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) (j : Fin 3) :
    inner ℝ (energyGradient j (J hDensity hSob n u))
      (Complex.I • energyGradient j (deltaJ hDensity hSob n u)) = 0 := by
  rw [J_gradient, deltaJ_gradient]
  exact (cutoff n).real_inner_I_cross_eq_zero (laplaceCutoff n)
    (star_symbol n) (laplaceSymbol_real n) (energyGradient j u)

end Actual
#print axioms l2_real_inner_eq_re
#print axioms BoundedSymbol.l2_commute
#print axioms BoundedSymbol.real_inner_I_cross_eq_zero
#print axioms Actual.laplaceSymbol_real
#print axioms Actual.regularized_kinetic_laplacian_zero
end HartreeF.Regularization
