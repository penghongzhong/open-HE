import FOrthogonalityCutoff

/-! Power-bound adapters for the explicitly conditional scalar assembly.
No analytic field or convolution is defined or assumed to converge in this file. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Filter
open scoped Topology ENNReal NNReal
namespace HartreeF.OrthogonalityCutoff

/-- A finite coefficient times a positive power of `2/R` tends to zero. -/
theorem tendsto_scale_envelope (C : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun R : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal ((2/R)^δ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun R : ℝ => 2/R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.const_mul (2 : ℝ))
  have hp := ENNReal.tendsto_ofReal (hi.rpow_const_nhds_zero hδ)
  simpa only [ENNReal.ofReal_zero, mul_zero] using
    ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hp (Or.inr ENNReal.coe_ne_top)

/-- A finite coefficient times a strictly negative power tends to zero. -/
theorem tendsto_spatial_envelope (C : ℝ≥0) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun X : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal (X^(-γ))) atTop (𝓝 0) := by
  have hp := ENNReal.tendsto_ofReal (tendsto_rpow_neg_atTop hγ)
  simpa only [ENNReal.ofReal_zero, mul_zero] using
    ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) hp (Or.inr ENNReal.coe_ne_top)

/-- Conditional scalar compact-orthogonality assembly with the exact normalized
analytic inputs: positive-power scale decay, negative-power spatial decay past
`K*(R+2)`, and exact temporal vanishing past `L*R`. Here `R=r+r⁻¹`.

The conclusion is over the original filter, with no subsequence. To obtain an
analytic theorem, all three bound hypotheses must be proved for the actual norm. -/
theorem tendsto_zero_of_ratio_spatial_temporal {ι : Type*} {l : Filter ι}
    {N : ι → ℝ≥0∞} {r X T : ι → ℝ} (hr : ∀ i, 0 < r i)
    (Cs Cx : ℝ≥0) {δ γ K L : ℝ}
    (hδ : 0 < δ) (hγ : 0 < γ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (horth : Tendsto (fun i => r i + (r i)⁻¹ + X i + T i) l atTop)
    (hscale : ∀ i, N i ≤ (Cs : ℝ≥0∞) *
      ENNReal.ofReal ((min (r i) (r i)⁻¹)^δ))
    (hspace : ∀ i, K * (r i + (r i)⁻¹ + 2) < X i →
      N i ≤ (Cx : ℝ≥0∞) * ENNReal.ofReal ((X i)^(-γ)))
    (htime : ∀ i, L * (r i + (r i)⁻¹) < T i → N i = 0) :
    Tendsto N l (𝓝 0) := by
  apply tendsto_zero_of_three_cutoffs (R := fun i => r i + (r i)⁻¹) horth
  · intro ε hε
    obtain ⟨A, hA⟩ := eventually_atTop.mp
      ((ENNReal.tendsto_nhds_zero.mp (tendsto_scale_envelope Cs hδ)) ε hε)
    refine ⟨A, fun i hi => (hscale i).trans ?_⟩
    apply le_trans _ (hA _ hi)
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow (le_min (hr i).le (inv_pos.mpr (hr i)).le)
      (min_le_two_div_sum (hr i) (inv_pos.mpr (hr i)) (mul_inv_cancel₀ (hr i).ne')) hδ.le
  · intro A ε hε
    obtain ⟨B, hB⟩ := eventually_atTop.mp
      ((ENNReal.tendsto_nhds_zero.mp (tendsto_spatial_envelope Cx hγ)) ε hε)
    refine ⟨max B (K*(A+2)+1), fun i hRi hXi => ?_⟩
    have hX : K*(r i + (r i)⁻¹+2) < X i := by
      have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hRi 2) hK
      have hlarge := (le_max_right B (K*(A+2)+1)).trans hXi
      linarith
    exact (hspace i hX).trans (hB (X i) ((le_max_left _ _).trans hXi))
  · intro A
    refine ⟨L*A+1, fun i hRi hTi => htime i ?_⟩
    have hmul := mul_le_mul_of_nonneg_left hRi hL
    linarith

#print axioms tendsto_scale_envelope
#print axioms tendsto_spatial_envelope
#print axioms tendsto_zero_of_ratio_spatial_temporal
end HartreeF.OrthogonalityCutoff
