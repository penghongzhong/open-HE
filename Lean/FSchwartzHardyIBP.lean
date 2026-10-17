import FRegularizedHardyFieldBounds
import FEnergySchwartzDensity
import FEnergyGradientNorm
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Author candidate imported from preserved uncompiled proof text.
Exact per-attempt native receipts determine status. All analytic domain,
integrability, derivative and IBP claims are proved in the source below.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory LineDeriv
open scoped ENNReal SchwartzMap RealInnerProductSpace
namespace HartreeF.RegularizedHardy
open EnergySpace

/-- Actual Schwartz coordinate derivative, retaining its complex codomain. -/
def schwartzDerivative (φ : Test) (j : Fin 3) : Test := ∂_{coordinate j} φ

def density (φ : Test) (x : V) : ℝ := ‖φ x‖^2

def crossTerm (φ : Test) (j : Fin 3) (x : V) : ℝ :=
  (star (φ x) * schwartzDerivative φ j x).re

def gradientDensity (φ : Test) (x : V) : ℝ :=
  ∑ j : Fin 3, ‖schwartzDerivative φ j x‖^2

def fluxDensity (ε : ℝ) (y : V) (φ : Test) (x : V) : ℝ :=
  ∑ j : Fin 3, component ε y j x * crossTerm φ j x

lemma schwartzDerivative_apply (φ : Test) (j : Fin 3) (x : V) :
    schwartzDerivative φ j x = fderiv ℝ φ x (coordinate j) :=
  SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _

lemma complex_real_inner (a b : ℂ) : inner ℝ a b = (star a * b).re := by
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply']
  rfl

lemma density_nonneg (φ : Test) (x : V) : 0 ≤ density φ x := sq_nonneg _

lemma density_continuous (φ : Test) : Continuous (density φ) := φ.continuous.norm.pow 2

lemma density_differentiable (φ : Test) : Differentiable ℝ (density φ) :=
  fun x => (φ.hasFDerivAt x).norm_sq.differentiableAt

/-- Differentiation of the actual complex squared norm, with both real and imaginary coordinates retained. -/
lemma density_fderiv (φ : Test) (j : Fin 3) (x : V) :
    fderiv ℝ (density φ) x (coordinate j) = 2 * crossTerm φ j x := by
  change fderiv ℝ (fun z => ‖φ z‖^2) x (coordinate j) = _
  rw [(φ.hasFDerivAt x).norm_sq.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat, complex_real_inner,
    crossTerm, schwartzDerivative_apply]

lemma crossTerm_continuous (φ : Test) (j : Fin 3) : Continuous (crossTerm φ j) :=
  Complex.continuous_re.comp (φ.continuous.star.mul (schwartzDerivative φ j).continuous)

lemma crossTerm_norm_le (φ : Test) (j : Fin 3) (x : V) :
    ‖crossTerm φ j x‖ ≤ ‖φ x‖ * ‖schwartzDerivative φ j x‖ := by
  simpa only [crossTerm, Real.norm_eq_abs, norm_mul, norm_star] using
    Complex.abs_re_le_norm (star (φ x) * schwartzDerivative φ j x)

lemma density_derivative_norm_le (φ : Test) (j : Fin 3) (x : V) :
    ‖fderiv ℝ (density φ) x (coordinate j)‖ ≤
      2 * ‖φ x‖ * ‖schwartzDerivative φ j x‖ := by
  calc
    _ = 2 * ‖crossTerm φ j x‖ := by rw [density_fderiv, norm_mul]; norm_num
    _ ≤ 2 * (‖φ x‖ * ‖schwartzDerivative φ j x‖) :=
      mul_le_mul_of_nonneg_left (crossTerm_norm_le φ j x) (by norm_num)
    _ = _ := by ring

/-- Schwartz L2, rather than any L2 assumption on a general EnergyState value. -/
lemma density_integrable (φ : Test) : Integrable (density φ) volume :=
  (φ.memLp 2 volume).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

lemma derivative_sq_integrable (φ : Test) (j : Fin 3) :
    Integrable (fun x => ‖schwartzDerivative φ j x‖^2) volume :=
  ((schwartzDerivative φ j).memLp 2 volume).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)

lemma crossTerm_integrable (φ : Test) (j : Fin 3) :
    Integrable (crossTerm φ j) volume := by
  have hprod : Integrable (fun x => ‖φ x‖ * ‖schwartzDerivative φ j x‖) volume := by
    exact (φ.memLp 2 volume).norm.integrable_mul
        ((schwartzDerivative φ j).memLp 2 volume).norm
  exact hprod.mono' (crossTerm_continuous φ j).aestronglyMeasurable
    (Filter.Eventually.of_forall (crossTerm_norm_le φ j))

lemma density_derivative_integrable (φ : Test) (j : Fin 3) :
    Integrable (fun x => fderiv ℝ (density φ) x (coordinate j)) volume := by
  simpa only [density_fderiv] using (crossTerm_integrable φ j).const_mul 2

lemma density_component_integrable {ε : ℝ} (hε : 0 < ε)
    (y : V) (φ : Test) (j : Fin 3) :
    Integrable (fun x => density φ x * component ε y j x) volume :=
  (density_integrable φ).mul_bdd (component_continuous hε y j).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => component_norm_le hε y x j))

lemma density_diagonal_integrable {ε : ℝ} (hε : 0 < ε)
    (y : V) (φ : Test) (j : Fin 3) :
    Integrable (fun x => density φ x *
      fderiv ℝ (component ε y j) x (coordinate j)) volume :=
  (density_integrable φ).mul_bdd (diagonal_continuous hε y j).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => diagonal_norm_le hε y x j))

lemma component_crossTerm_integrable {ε : ℝ} (hε : 0 < ε)
    (y : V) (φ : Test) (j : Fin 3) :
    Integrable (fun x => component ε y j x * crossTerm φ j x) volume :=
  (crossTerm_integrable φ j).bdd_mul (component_continuous hε y j).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => component_norm_le hε y x j))

lemma derivative_component_integrable {ε : ℝ} (hε : 0 < ε)
    (y : V) (φ : Test) (j : Fin 3) :
    Integrable (fun x => fderiv ℝ (density φ) x (coordinate j) *
      component ε y j x) volume :=
  (density_derivative_integrable φ j).mul_bdd
    (component_continuous hε y j).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => component_norm_le hε y x j))

lemma density_divergence_integrable {ε : ℝ} (hε : 0 < ε)
    (y : V) (φ : Test) :
    Integrable (fun x => density φ x * divergence ε y x) volume := by
  simp only [divergence, Finset.mul_sum]
  exact integrable_finsetSum _ (fun j _ => density_diagonal_integrable hε y φ j)

lemma fluxDensity_integrable {ε : ℝ} (hε : 0 < ε) (y : V) (φ : Test) :
    Integrable (fluxDensity ε y φ) volume :=
  integrable_finsetSum _ (fun j _ => component_crossTerm_integrable hε y φ j)

lemma gradientDensity_integrable (φ : Test) : Integrable (gradientDensity φ) volume :=
  integrable_finsetSum _ (fun j _ => derivative_sq_integrable φ j)

/-- Literal Mathlib integration by parts; all three integrability facts are produced. -/
theorem schwartz_component_ibp {ε : ℝ} (hε : 0 < ε)
    (y : V) (φ : Test) (j : Fin 3) :
    (∫ x, density φ x * fderiv ℝ (component ε y j) x (coordinate j)) =
      -(∫ x, fderiv ℝ (density φ) x (coordinate j) * component ε y j x) := by
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (derivative_component_integrable hε y φ j)
    (density_diagonal_integrable hε y φ j)
    (density_component_integrable hε y φ j)
    (fun x _ => density_differentiable φ x)
    (fun x _ => (component_hasFDerivAt hε y x j).differentiableAt)

/-- Genuine summed identity for the native divergence and actual Schwartz function. -/
theorem schwartz_divergence_ibp {ε : ℝ} (hε : 0 < ε) (y : V) (φ : Test) :
    (∫ x, density φ x * divergence ε y x) =
      -2 * (∫ x, fluxDensity ε y φ x) := by
  calc
    (∫ x, density φ x * divergence ε y x) =
        ∑ j : Fin 3, ∫ x, density φ x *
          fderiv ℝ (component ε y j) x (coordinate j) := by
      simp only [divergence, Finset.mul_sum]
      rw [integral_finsetSum _ (fun j _ => density_diagonal_integrable hε y φ j)]
    _ = ∑ j : Fin 3, -(∫ x, fderiv ℝ (density φ) x (coordinate j) *
        component ε y j x) := by
      exact Finset.sum_congr rfl (fun j _ => schwartz_component_ibp hε y φ j)
    _ = ∑ j : Fin 3, -2 * (∫ x, component ε y j x * crossTerm φ j x) := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [density_fderiv]
      have heq : (fun x => 2 * crossTerm φ j x * component ε y j x) =
          (fun x => 2 * (component ε y j x * crossTerm φ j x)) := by
        funext x
        ring
      rw [heq, integral_const_mul]
      ring
    _ = -2 * (∫ x, fluxDensity ε y φ x) := by
      rw [← Finset.mul_sum]
      congr 1
      exact (integral_finsetSum _
        (fun j _ => component_crossTerm_integrable hε y φ j)).symm

/-- Exact kinetic identification; there is no dimension or real/imaginary loss. -/
theorem schwartz_gradient_integral (φ : Test) :
    (∫ x, gradientDensity φ x) = gradientSquared (schwartzEnergyState φ) := by
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  unfold gradientDensity gradientSquared
  rw [integral_finsetSum _ (fun j _ => derivative_sq_integrable φ j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [schwartzEnergyState_gradient, energyLp_norm_pow (n := 2) (by decide)]
  apply integral_congr_ae
  filter_upwards [(schwartzDerivative φ j).coeFn_toLp 2 volume] with x hx
  change ‖schwartzDerivative φ j x‖^2 =
    ‖((schwartzDerivative φ j).toLp 2 volume) x‖^2
  rw [hx]

end HartreeF.RegularizedHardy
