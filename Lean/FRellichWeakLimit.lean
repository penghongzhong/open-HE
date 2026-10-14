import FOrdinaryRellichBall

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalRellich

/-- Sequential precompactness plus genuine Hilbert weak convergence identifies
all strong cluster limits and therefore the limit of the whole sequence. -/
theorem tendsto_of_weak_of_subsequence_cauchy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : ℕ → E} {f : E}
    (hweak : ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) atTop (𝓝 (inner ℝ f v)))
    (hc : ∀ σ : ℕ → ℕ, StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ CauchySeq (fun n => u (σ (τ n)))) :
    Tendsto u atTop (𝓝 f) := by
  by_contra h
  rw [Metric.tendsto_atTop'] at h
  push Not at h
  obtain ⟨ε,hε,hbad⟩ := h
  obtain ⟨σ,hσ,hσbad⟩ := Nat.exists_strictMono_subsequence hbad
  obtain ⟨τ,hτ,hcτ⟩ := hc σ hσ
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hcτ
  have hgf : g=f := by
    apply ext_inner_right ℝ
    intro v
    exact tendsto_nhds_unique (hg.inner tendsto_const_nhds)
      ((hweak v).comp (hσ.comp hτ).tendsto_atTop)
  rw [hgf] at hg
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hg ε hε
  exact (not_lt_of_ge (hσbad (τ N))) (hN N le_rfl)

#print axioms tendsto_of_weak_of_subsequence_cauchy
end HartreeF.LocalRellich
