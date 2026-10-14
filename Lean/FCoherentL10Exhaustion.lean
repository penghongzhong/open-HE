import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
set_option warningAsError true

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FEndpoint

local instance : Fact (1 ≤ (10 : ℝ≥0∞)) := ⟨by norm_num⟩

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α}

/-- Uniformly bounded, coherent L¹⁰ truncations have a global L¹⁰ realization.
No inner-product structure, completeness, or finite measure hypothesis is used.
The support sets need not be measurable: all support and agreement assertions
are formulated almost everywhere in the ambient measure. -/
theorem exists_coherent_L10_exhaustion
    (S : ℕ → Set α) (f : ℕ → Lp E 10 μ) (C : ℝ)
    (hbound : ∀ n, ‖f n‖ ≤ C)
    (hsupport : ∀ n, ∀ᵐ x ∂μ, x ∉ S n → f n x = 0)
    (hcoherent : ∀ n m, n ≤ m → ∀ᵐ x ∂μ, x ∈ S n → f m x = f n x) :
    ∃ F : Lp E 10 μ, ‖F‖ ≤ C ∧
      (∀ n, ∀ᵐ x ∂μ, x ∈ S n → F x = f n x) ∧
      (∀ᵐ x ∂μ, x ∉ ⋃ n, S n → F x = 0) := by
  have hs : ∀ᵐ x ∂μ, ∀ n, x ∉ S n → f n x = 0 := ae_all_iff.mpr hsupport
  have hc : ∀ᵐ x ∂μ, ∀ n m, n ≤ m → x ∈ S n → f m x = f n x := by
    refine ae_all_iff.mpr fun n => ae_all_iff.mpr fun m => ?_
    by_cases hnm : n ≤ m
    · filter_upwards [hcoherent n m hnm] with x hx using fun _ => hx
    · exact Filter.Eventually.of_forall fun _ h => (hnm h).elim
  have hex : ∀ᵐ x ∂μ, ∃ l : E, Tendsto (fun n => f n x) atTop (𝓝 l) := by
    filter_upwards [hs, hc] with x hxs hxc
    by_cases hx : ∃ n, x ∈ S n
    · obtain ⟨n, hn⟩ := hx
      refine ⟨f n x, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [eventually_ge_atTop n] with m hm
      exact (hxc n m hm hn).symm
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      exact Filter.Eventually.of_forall fun n => (hxs n (fun hn => hx ⟨n, hn⟩)).symm
  obtain ⟨g, hgm, hlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae
    (fun n => Lp.aestronglyMeasurable (f n)) hex
  have hg_bound : eLpNorm g 10 μ ≤ ENNReal.ofReal C := by
    apply Lp.eLpNorm_le_of_ae_tendsto _ (fun n => Lp.aestronglyMeasurable (f n))
      hgm.aestronglyMeasurable hlim
    exact Filter.Eventually.of_forall fun n => by
      rw [← Lp.enorm_def, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbound n)
  have hgp : MemLp g 10 μ := hg_bound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hgp.toLp g, ?_, ?_, ?_⟩
  · rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hg_bound).trans_eq
      (ENNReal.toReal_ofReal ((norm_nonneg (f 0)).trans (hbound 0)))
  · intro n
    filter_upwards [MemLp.coeFn_toLp hgp, hlim, hc] with x hx hxl hxc
    intro hxn
    rw [hx]
    apply tendsto_nhds_unique hxl
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    exact (hxc n m hm hxn).symm
  · filter_upwards [MemLp.coeFn_toLp hgp, hlim, hs] with x hx hxl hxs
    intro hxn
    rw [hx]
    apply tendsto_nhds_unique hxl
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun n =>
      (hxs n (fun hn => hxn (mem_iUnion.mpr ⟨n, hn⟩))).symm

end FEndpoint

#print axioms FEndpoint.exists_coherent_L10_exhaustion
