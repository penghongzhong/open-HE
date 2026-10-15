import F121BoundedAffineClosed

/-! R8.4 Theorem 5.8, page 42: pointwise closed-half-line limits and
splicing of normalizing parameters. The trajectory itself is never spliced. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Filter Set
open scoped Topology
namespace HartreeF.Paper121PointwiseNormalization
open EnergySpace CriticalAffine SobolevStretch Paper121AffineClosed

theorem halfline_mem_of_expanding_windows {Cs : ℝ} (hSob : OrdinarySobolev Cs)
    {K : Set EnergyState} (hK : IsCompact K) (hKzero : (0 : EnergyState) ∉ K)
    (B sigma : ℝ) (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (v : ℕ → ℝ → EnergyState) (w : ℝ → EnergyState)
    (hv : ∀ t, Tendsto (fun n => v n t) atTop (𝓝 (w t)))
    (hwindow : ∀ n t, 0 ≤ sigma * t → sigma * t ≤ L n →
      v n t ∈ boundedAffineCarrier K B) :
    ∀ t, 0 ≤ sigma * t → w t ∈ boundedAffineCarrier K B := by
  intro t ht
  apply boundedAffineCarrier_mem_of_tendsto hSob hK hKzero (hv t)
  exact (hL.eventually (eventually_ge_atTop (sigma * t))).mono
    (fun n hn => hwindow n t ht hn)

theorem splice_pointwise_normalizers
    (w : ℝ → EnergyState) (sigma B : ℝ) (K Q : Set EnergyState)
    (hK : IsCompact K) (hQ : IsCompact Q)
    (hhalf : ∀ t, 0 ≤ sigma * t → w t ∈ boundedAffineCarrier K B)
    (r0 : ℝ → ℝ) (hr0 : ∀ t, 0 < r0 t) (y0 : ℝ → Space)
    (hglobal : ∀ t, (criticalAffineState (r0 t) (hr0 t) (y0 t)).symm (w t) ∈ Q) :
    ∃ (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space),
      IsCompact (K ∪ Q) ∧
      (∀ t, (criticalAffineState (r t) (hr t) (y t)).symm (w t) ∈ K ∪ Q) ∧
      ∀ t, 0 ≤ sigma * t → r t ≤ B := by
  classical
  have hex (t : ℝ) : ∃ (b : ℝ) (hb : 0 < b) (c : Space),
      (criticalAffineState b hb c).symm (w t) ∈ K ∪ Q ∧
      (0 ≤ sigma * t → b ≤ B) := by
    by_cases ht : 0 ≤ sigma * t
    · obtain ⟨h, hh, b, hb, c, hbB, heq⟩ := hhalf t ht
      refine ⟨b, hb, c, ?_, fun _ => hbB⟩
      rw [heq, LinearIsometryEquiv.symm_apply_apply]
      exact Or.inl hh
    · exact ⟨r0 t, hr0 t, y0 t, Or.inr (hglobal t), fun ht' => (ht ht').elim⟩
  choose r hr y hmem hbound using hex
  exact ⟨r, hr, y, hK.union hQ, hmem, hbound⟩

end HartreeF.Paper121PointwiseNormalization
