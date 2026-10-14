import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-! Conditional scalar assembly for compact-profile orthogonality.
This file proves no convolution estimate. Its hypotheses must be supplied by
actual analytic scale, spatial, and temporal estimates. All cutoffs are uniform
on the whole index filter; no profile-dependent subsequence is chosen. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Filter
open scoped Topology ENNReal NNReal
namespace HartreeF.OrthogonalityCutoff

/-- Uniform three-region cutoff assembly. This is only a scalar implication;
`hscale`, `hspace`, and `htime` are explicit estimate inputs. -/
theorem tendsto_zero_of_three_cutoffs {ι : Type*} {l : Filter ι}
    {N : ι → ℝ≥0∞} {R X T : ι → ℝ}
    (horth : Tendsto (fun i => R i + X i + T i) l atTop)
    (hscale : ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : ℝ, ∀ i, A ≤ R i → N i ≤ ε)
    (hspace : ∀ A : ℝ, ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ B : ℝ, ∀ i, R i ≤ A → B ≤ X i → N i ≤ ε)
    (htime : ∀ A : ℝ, ∃ D : ℝ, ∀ i, R i ≤ A → D ≤ T i → N i = 0) :
    Tendsto N l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := hscale ε hε
  obtain ⟨B, hB⟩ := hspace A ε hε
  obtain ⟨D, hD⟩ := htime A
  filter_upwards [horth.eventually (eventually_ge_atTop (A + B + D))] with i hi
  by_cases hR : A ≤ R i
  · exact hA i hR
  have hRi : R i ≤ A := le_of_not_ge hR
  by_cases hX : B ≤ X i
  · exact hB i hRi hX
  have hTi : D ≤ T i := by linarith
  rw [hD i hRi hTi]
  exact hε.le

/-- Two positive reciprocal ratios have minimum at most twice the inverse sum. -/
theorem min_le_two_div_sum {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q*r = 1) :
    min q r ≤ 2/(q+r) := by
  apply (le_div_iff₀ (add_pos hq hr)).mpr
  rcases le_total q r with h | h
  · rw [min_eq_left h]
    have hq1 : q ≤ 1 := by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr h)]
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hq1)]
  · rw [min_eq_right h]
    have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr h)]
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1)]

#print axioms tendsto_zero_of_three_cutoffs
#print axioms min_le_two_div_sum
end HartreeF.OrthogonalityCutoff
