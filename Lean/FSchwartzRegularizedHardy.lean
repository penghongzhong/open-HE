import FSchwartzHardyIBP

/-!
Author candidate imported from preserved uncompiled proof text.
Exact per-attempt native receipts determine status. All analytic domain,
integrability, derivative and IBP claims are proved in the source below.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace HartreeF.RegularizedHardy
open EnergySpace

def regularizedDensity (ε : ℝ) (y : V) (φ : Test) (x : V) : ℝ :=
  density φ x * (denominator ε y x)⁻¹

lemma regularizedDensity_integrable {ε : ℝ} (hε : 0 < ε) (y : V) (φ : Test) :
    Integrable (regularizedDensity ε y φ) volume := by
  apply (density_integrable φ).mul_bdd (inverse_continuous hε y).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (denominator_pos hε y x))]
    exact inverse_le hε y x)

lemma density_field_norm_sq_integrable {ε : ℝ} (hε : 0 < ε)
    (y : V) (φ : Test) :
    Integrable (fun x => density φ x * ‖field ε y x‖^2) volume := by
  apply (density_integrable φ).mul_bdd
    ((field_continuous hε y).norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact field_norm_sq_le hε y x)

/-- Coordinate Young, summed before integration, preserves the exact constant. -/
lemma flux_pointwise_le {ε : ℝ} (hε : 0 < ε) (y : V) (φ : Test) (x : V) :
    -2 * fluxDensity ε y φ x ≤
      (1 / 2 : ℝ) * regularizedDensity ε y φ x + 2 * gradientDensity φ x := by
  have hsum :
      (∑ j : Fin 3, -(2 * component ε y j x * crossTerm φ j x)) ≤
      ∑ j : Fin 3, ((1 / 2 : ℝ) * (component ε y j x)^2 * density φ x +
        2 * ‖schwartzDerivative φ j x‖^2) := by
    apply Finset.sum_le_sum
    intro j _
    exact complex_coordinate_young (φ x) (schwartzDerivative φ j x)
      (component ε y j x)
  have hleft : (∑ j : Fin 3, -(2 * component ε y j x * crossTerm φ j x)) =
      -2 * fluxDensity ε y φ x := by
    unfold fluxDensity
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hright :
      (∑ j : Fin 3, ((1 / 2 : ℝ) * (component ε y j x)^2 * density φ x +
        2 * ‖schwartzDerivative φ j x‖^2)) =
      (1 / 2 : ℝ) * density φ x * ‖field ε y x‖^2 + 2 * gradientDensity φ x := by
    rw [← component_sq_sum]
    simp only [gradientDensity, Fin.sum_univ_three]
    ring
  rw [hleft, hright] at hsum
  calc
    -2 * fluxDensity ε y φ x ≤
        (1 / 2 : ℝ) * density φ x * ‖field ε y x‖^2 +
          2 * gradientDensity φ x := hsum
    _ ≤ (1 / 2 : ℝ) * regularizedDensity ε y φ x +
          2 * gradientDensity φ x := by
      unfold regularizedDensity
      have h := mul_le_mul_of_nonneg_left (field_norm_sq_le_inverse hε y x)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (density_nonneg φ x))
      nlinarith

/-- Genuine regularized Hardy estimate for an actual Schwartz function. -/
theorem schwartz_regularized_hardy {ε : ℝ} (hε : 0 < ε) (y : V) (φ : Test) :
    (∫ x, regularizedDensity ε y φ x) ≤
      4 * gradientSquared (schwartzEnergyState φ) := by
  have hI := regularizedDensity_integrable hε y φ
  have hJ := density_divergence_integrable hε y φ
  have hF := fluxDensity_integrable hε y φ
  have hE := gradientDensity_integrable φ
  have hlower : (∫ x, regularizedDensity ε y φ x) ≤
      ∫ x, density φ x * divergence ε y x := by
    apply integral_mono hI hJ
    intro x
    exact mul_le_mul_of_nonneg_left (inverse_le_divergence hε y x) (density_nonneg φ x)
  have hupper : (∫ x, -2 * fluxDensity ε y φ x) ≤
      ∫ x, ((1 / 2 : ℝ) * regularizedDensity ε y φ x + 2 * gradientDensity φ x) :=
    integral_mono (hF.const_mul (-2)) ((hI.const_mul (1 / 2 : ℝ)).add (hE.const_mul 2))
      (flux_pointwise_le hε y φ)
  rw [integral_const_mul, integral_add (hI.const_mul (1 / 2 : ℝ)) (hE.const_mul 2),
    integral_const_mul, integral_const_mul, schwartz_gradient_integral] at hupper
  rw [schwartz_divergence_ibp hε y φ] at hlower
  linarith

/-- Public producer: finiteness and bound, with no desired-estimate premise. -/
theorem schwartz_regularized_hardy_integrable_and_bound
    {ε : ℝ} (hε : 0 < ε) (y : V) (φ : Test) :
    Integrable (fun x : V => ‖φ x‖^2 / (ε + ‖x - y‖^2)) volume ∧
    (∫ x : V, ‖φ x‖^2 / (ε + ‖x - y‖^2)) ≤
      4 * gradientSquared (schwartzEnergyState φ) := by
  have heq : (fun x : V => ‖φ x‖^2 / (ε + ‖x - y‖^2)) =
      regularizedDensity ε y φ := by
    funext x
    rw [div_eq_mul_inv]
    rfl
  rw [heq]
  exact ⟨regularizedDensity_integrable hε y φ, schwartz_regularized_hardy hε y φ⟩

end HartreeF.RegularizedHardy
