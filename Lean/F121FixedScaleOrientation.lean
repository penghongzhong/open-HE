import F121NearMaxScale

/-! A fixed sign is selected on one subsequence, before any time is fixed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped Topology
namespace HartreeF.Paper121ScaleSelection

theorem fixed_long_direction (ell q : ℕ → ℝ)
    (hlength : Tendsto (fun n => ell n + q n) atTop atTop) :
    ∃ (σ : ℝ) (k : ℕ → ℕ), (σ = 1 ∨ σ = -1) ∧ StrictMono k ∧
      Tendsto (fun n => max (ell (k n)) (q (k n))) atTop atTop ∧
      ∀ n, (σ = 1 ∧ ell (k n) ≤ q (k n)) ∨ (σ = -1 ∧ q (k n) ≤ ell (k n)) := by
  have hmax : Tendsto (fun n => max (ell n) (q n)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hlength.eventually (eventually_ge_atTop (2 * b))] with n hn
    have h1 := le_max_left (ell n) (q n)
    have h2 := le_max_right (ell n) (q n)
    linarith
  by_cases hf : ∃ᶠ n in atTop, ell n ≤ q n
  · obtain ⟨k, hk, hkn⟩ := extraction_of_frequently_atTop hf
    exact ⟨1, k, Or.inl rfl, hk, hmax.comp hk.tendsto_atTop,
      fun n => Or.inl ⟨rfl, hkn n⟩⟩
  · have he : ∀ᶠ n in atTop, q n ≤ ell n := by
      have hn : ∀ᶠ n in atTop, ¬ ell n ≤ q n := not_frequently.mp hf
      exact hn.mono fun _ h => (lt_of_not_ge h).le
    obtain ⟨k, hk, hkn⟩ := extraction_of_eventually_atTop he
    exact ⟨-1, k, Or.inr rfl, hk, hmax.comp hk.tendsto_atTop,
      fun n => Or.inr ⟨rfl, hkn n⟩⟩

theorem oriented_time_in_window {T τ a σ s : ℝ} (ha : 0 < a)
    (hτ : τ ∈ Icc 0 T)
    (hdir : (σ = 1 ∧ τ / a ^ 2 ≤ (T - τ) / a ^ 2) ∨
      (σ = -1 ∧ (T - τ) / a ^ 2 ≤ τ / a ^ 2))
    (hs0 : 0 ≤ σ * s)
    (hsL : σ * s ≤ max (τ / a ^ 2) ((T - τ) / a ^ 2)) :
    τ + a ^ 2 * s ∈ Icc 0 T := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  rcases hdir with ⟨rfl, hright⟩ | ⟨rfl, hleft⟩
  · rw [max_eq_right hright, one_mul] at hsL
    simp only [one_mul] at hs0
    have hupper := (le_div_iff₀ ha2).mp hsL
    have hpos := mul_nonneg ha2.le hs0
    constructor <;> nlinarith [hτ.1]
  · rw [max_eq_left hleft, neg_one_mul] at hsL
    simp only [neg_one_mul] at hs0
    have hlower := (le_div_iff₀ ha2).mp hsL
    have hnonpos : a ^ 2 * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha2.le (by linarith)
    constructor <;> nlinarith [hτ.2]

end HartreeF.Paper121ScaleSelection
