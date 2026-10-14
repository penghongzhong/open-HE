import FComplementaryPowerSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcingL2
open TimeHolder GradientMajorants

/-- Exact extended-valued budget for the actual L² forcing difference. -/
def forcingBudget (alpha : ℝ) (M S D E : ℝ≥0∞) : ℝ≥0∞ :=
  M ^ (2 * alpha) * S ^ (4 : ℝ) * E +
    M ^ (5 * alpha / 3) * S ^ (4 + alpha / 3) * D ^ (alpha / 3) * E ^ (1 - alpha / 3)

/-- Simultaneous E/S convergence is linear after a common bound delta. -/
theorem forcingBudget_le_delta {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    (M S D E delta : ℝ≥0∞) (hD : D ≤ delta) (hE : E ≤ delta) :
    forcingBudget alpha M S D E ≤
      (M ^ (2 * alpha) * S ^ (4 : ℝ) +
        M ^ (5 * alpha / 3) * S ^ (4 + alpha / 3)) * delta := by
  have hp : D ^ (alpha / 3) * E ^ (1 - alpha / 3) ≤ delta := by
    have he : theta alpha = 1 - alpha / 3 := by unfold theta; ring
    simpa only [he] using ennreal_complementary_power_smallness ha ha3 hD hE
  unfold forcingBudget
  calc
    _ ≤ M ^ (2 * alpha) * S ^ (4 : ℝ) * delta +
        (M ^ (5 * alpha / 3) * S ^ (4 + alpha / 3)) * delta :=
      add_le_add (mul_le_mul' le_rfl hE) (by simpa only [mul_assoc] using mul_le_mul' (le_refl (M ^ (5 * alpha / 3) * S ^ (4 + alpha / 3))) hp)
    _ = _ := (add_mul _ _ _).symm

theorem forcingBudget_mono {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {M S D E M' S' D' E' : ℝ≥0∞}
    (hM : M ≤ M') (hS : S ≤ S') (hD : D ≤ D') (hE : E ≤ E') :
    forcingBudget alpha M S D E ≤ forcingBudget alpha M' S' D' E' := by
  have ha2 : 0 ≤ 2 * alpha := by positivity
  have ha5 : 0 ≤ 5 * alpha / 3 := by positivity
  have ha4 : 0 ≤ 4 + alpha / 3 := by positivity
  have ha1 : 0 ≤ 1 - alpha / 3 := by linarith
  unfold forcingBudget
  gcongr

/-- This scalar continuity bridge also applies to other finite analytic budgets.
Only a vanishing error and a finite coefficient are required. -/
theorem tendsto_zero_of_finite_coefficient {I : Type*} {l : Filter I}
    {a d : I → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hd : Tendsto d l (𝓝 0)) (hbound : ∀ i, a i ≤ B * d i) :
    Tendsto a l (𝓝 0) := by
  have ht : Tendsto (fun i => B * d i) l (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hd (Or.inr hB)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hbound

/-- Explicit convergence in the two input mixed norms gives a vanishing budget. -/
theorem forcingBudget_tendsto_zero {I : Type*} {l : Filter I} {alpha : ℝ}
    (ha : 0 < alpha) (ha3 : alpha < 3) (M S : ℝ≥0∞) (hM : M ≠ ∞) (hS : S ≠ ∞)
    (D E : I → ℝ≥0∞) (hD : Tendsto D l (𝓝 0)) (hE : Tendsto E l (𝓝 0)) :
    Tendsto (fun i => forcingBudget alpha M S (D i) (E i)) l (𝓝 0) := by
  apply tendsto_zero_of_finite_coefficient
    (B := M ^ (2 * alpha) * S ^ (4 : ℝ) + M ^ (5 * alpha / 3) * S ^ (4 + alpha / 3))
    (d := fun i => D i + E i)
  · have ha2 : 0 ≤ 2 * alpha := by positivity
    have ha5 : 0 ≤ 5 * alpha / 3 := by positivity
    have ha4 : 0 ≤ 4 + alpha / 3 := by positivity
    finiteness
  · simpa only [add_zero] using hD.add hE
  · intro i
    exact forcingBudget_le_delta ha ha3 M S (D i) (E i) (D i + E i)
      le_self_add le_add_self

#print axioms forcingBudget_le_delta
#print axioms forcingBudget_mono
#print axioms tendsto_zero_of_finite_coefficient
#print axioms forcingBudget_tendsto_zero
end HartreeF.ForcingL2
