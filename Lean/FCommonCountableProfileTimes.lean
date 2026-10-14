import FNormalizedTimeSubsequence

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open Filter
open scoped Topology

namespace HartreeF.CommonProfileTimes

/-- A normalized profile time has a finite limit, tends to positive infinity,
or tends to negative infinity. The condition is on the actual real sequence. -/
def TimeRegime (s : ℕ → ℝ) : Prop :=
  (∃ t : ℝ, Tendsto s atTop (𝓝 t)) ∨
    Tendsto s atTop atTop ∨ Tendsto s atTop atBot

/-- Compactness is applied once to the countable product of extended-real
lines. This yields one strictly increasing subsequence for every label,
including inactive labels; it is not a family of label-dependent subsequences. -/
theorem exists_common_time_regimes (s : ℕ → ℕ → ℝ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ j : ℕ, TimeRegime (s j ∘ σ) := by
  obtain ⟨t, σ, hσ, ht⟩ :=
    CompactSpace.tendsto_subseq (fun n j : ℕ => (s j n : EReal))
  refine ⟨σ, hσ, fun j => ?_⟩
  have hj : Tendsto (fun n => (s j (σ n) : EReal)) atTop (𝓝 (t j)) :=
    (continuous_apply j).continuousAt.tendsto.comp ht
  generalize t j = r at hj
  induction r using EReal.rec with
  | bot => exact Or.inr (Or.inr (EReal.tendsto_coe_nhds_bot_iff.mp hj))
  | coe r => exact Or.inl ⟨r, EReal.tendsto_coe.mp hj⟩
  | top => exact Or.inr (Or.inl (EReal.tendsto_coe_nhds_top_iff.mp hj))

/-- Subsequent strictly increasing refinements preserve the selected regime. -/
theorem timeRegime_comp {s : ℕ → ℝ} (hs : TimeRegime s)
    {τ : ℕ → ℕ} (hτ : StrictMono τ) : TimeRegime (s ∘ τ) := by
  rcases hs with ⟨r, hr⟩ | hp | hn
  · exact Or.inl ⟨r, hr.comp hτ.tendsto_atTop⟩
  · exact Or.inr (Or.inl (hp.comp hτ.tendsto_atTop))
  · exact Or.inr (Or.inr (hn.comp hτ.tendsto_atTop))

end HartreeF.CommonProfileTimes
