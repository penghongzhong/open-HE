import F121FixedScaleOrientation

/-! R8.4 Theorem 5.8, the selection stage only. The limiting PDE trajectory,
closed bounded-scale affine carrier and final dilation are not asserted here. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped Topology
namespace HartreeF.Paper121ScaleSelection
open Paper121SubparabolicScalar

theorem select_compact_scale_windows {X : Type*} [MetricSpace X]
    (z : ℝ → X) (hcpt : IsCompact (closure (range z)))
    (r : ℝ → ℝ) (hr : ∀ t, 0 < r t)
    (hfinite : ∀ T : ℝ, 0 ≤ T → BddAbove (r '' Icc 0 T))
    (hsmall : Tendsto (fun T => runningScaleSupremum r T / Real.sqrt T) atTop (𝓝 0)) :
    ∃ (τ : ℕ → ℝ) (σ : ℝ) (k : ℕ → ℕ) (L : ℕ → ℝ) (psi : X),
      (∀ n, τ n ∈ Icc 0 ((n : ℝ) + 1) ∧
        runningScaleSupremum r ((n : ℝ) + 1) / 2 < r (τ n) ∧
        r (τ n) ≤ runningScaleSupremum r ((n : ℝ) + 1)) ∧
      (σ = 1 ∨ σ = -1) ∧ StrictMono k ∧ Tendsto L atTop atTop ∧
      psi ∈ closure (range z) ∧ Tendsto (fun n => z (τ (k n))) atTop (𝓝 psi) ∧
      ∀ n s, 0 ≤ σ * s → σ * s ≤ L n →
        τ (k n) + (r (τ (k n))) ^ 2 * s ∈ Icc 0 ((k n : ℝ) + 1) ∧
        0 < r (τ (k n) + (r (τ (k n))) ^ 2 * s) / r (τ (k n)) ∧
        r (τ (k n) + (r (τ (k n))) ^ 2 * s) / r (τ (k n)) < 2 := by
  classical
  let T : ℕ → ℝ := fun n => (n : ℝ) + 1
  let A : ℕ → ℝ := fun n => runningScaleSupremum r (T n)
  have hT (n : ℕ) : 0 < T n := by dsimp only [T]; positivity
  have hselect (n : ℕ) := exists_near_max_scale r hr (hT n).le (hfinite (T n) (hT n).le)
  choose τ hτ hnear hupper hratio using hselect
  let a : ℕ → ℝ := fun n => r (τ n)
  have hA (n : ℕ) : 0 < A n := (hr (τ n)).trans_le (hupper n)
  have hTtop : Tendsto T atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hsmallN : Tendsto (fun n => A n / Real.sqrt (T n)) atTop (𝓝 0) :=
    hsmall.comp hTtop
  have hlength := normalized_length_tendsto_atTop T A a hT hA
    (fun n => hr (τ n)) hupper hsmallN
  let ell : ℕ → ℝ := fun n => τ n / (a n) ^ 2
  let q : ℕ → ℝ := fun n => (T n - τ n) / (a n) ^ 2
  have hsum : Tendsto (fun n => ell n + q n) atTop atTop := by
    convert hlength using 1
    funext n
    dsimp only [ell, q]
    rw [← add_div]
    congr 1
    ring
  obtain ⟨σ, k, hσ, hk, hL, hdir⟩ := fixed_long_direction ell q hsum
  have hmem : ∃ᶠ n in atTop, z (τ (k n)) ∈ closure (range z) :=
    (Eventually.of_forall fun n => subset_closure (mem_range_self (τ (k n)))).frequently
  obtain ⟨psi, hpsi, j, hj, hz⟩ := hcpt.tendsto_subseq' hmem
  refine ⟨τ, σ, fun n => k (j n), fun n => max (ell (k (j n))) (q (k (j n))), psi,
    (fun n => ⟨hτ n, hnear n, hupper n⟩), hσ, hk.comp hj,
    hL.comp hj.tendsto_atTop, hpsi, hz, ?_⟩
  intro n s hs0 hsL
  have ht := oriented_time_in_window (hr (τ (k (j n)))) (hτ (k (j n)))
    (hdir (j n)) hs0 hsL
  exact ⟨ht, hratio (k (j n)) _ ht⟩

end HartreeF.Paper121ScaleSelection
