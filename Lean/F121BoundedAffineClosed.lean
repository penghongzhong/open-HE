import F121AffineCompactParameters
import Mathlib.Topology.Sequences

/-! R8.4 Theorem 5.8, page 42: closedness of the bounded-scale affine
family of a nonzero compact carrier. No compactness of that family is claimed.
The existing properness theorem supplies bounds along a convergent sequence. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped Topology
namespace HartreeF.Paper121AffineClosed
open EnergySpace CriticalAffine SobolevStretch Paper121AffineProperness

def boundedAffineCarrier (K : Set EnergyState) (B : ℝ) : Set EnergyState :=
  {g | ∃ h ∈ K, ∃ (b : ℝ) (hb : 0 < b) (c : Space),
    b ≤ B ∧ g = criticalAffineState b hb c h}

theorem boundedAffineCarrier_isClosed {Cs : ℝ} (hSob : OrdinarySobolev Cs)
    {K : Set EnergyState} (hK : IsCompact K) (hKzero : (0 : EnergyState) ∉ K)
    (B : ℝ) : IsClosed (boundedAffineCarrier K B) := by
  classical
  apply IsSeqClosed.isClosed
  intro g g0 hg hg0
  choose h hh b hb c hB heq using hg
  have hnorm (n : ℕ) : ‖g n‖ = ‖h n‖ := by
    rw [heq n, LinearIsometryEquiv.norm_map]
  have hgzero (n : ℕ) : g n ≠ 0 := by
    intro hz
    have hn : ‖h n‖ = 0 := by rw [← hnorm n, hz, norm_zero]
    exact hKzero ((norm_eq_zero.mp hn) ▸ hh n)
  obtain ⟨h0, hh0, j, hj, hlim⟩ := hK.tendsto_subseq hh
  have hnormlim : ‖g0‖ = ‖h0‖ := by
    apply tendsto_nhds_unique ((hg0.comp hj.tendsto_atTop).norm)
    simpa only [Function.comp_def, hnorm] using hlim.norm
  have hg0zero : g0 ≠ 0 := by
    intro hz
    have hn : ‖h0‖ = 0 := by rw [← hnormlim, hz, norm_zero]
    exact hKzero ((norm_eq_zero.mp hn) ▸ hh0)
  have hAzero : (0 : EnergyState) ∉ insert g0 (range g) := by
    rintro (hz | ⟨n, hn⟩)
    · exact hg0zero hz.symm
    · exact hgzero n hn
  obtain ⟨C, D, hC, hD, hbox⟩ :=
    compact_carriers_parameter_box hg0.isCompact_insert_range hAzero hK hKzero
  have hbbox (n : ℕ) : 1 / C ≤ b n ∧ b n ≤ C ∧ ‖c n‖ ≤ D := by
    apply hbox (g n) (mem_insert_of_mem _ (mem_range_self n)) (b n) (hb n) (c n)
    rw [heq n, LinearIsometryEquiv.symm_apply_apply]
    exact hh n
  have hprod : IsCompact (K ×ˢ (Icc (1 / C) B ×ˢ Metric.closedBall (0 : Space) D)) :=
    hK.prod (isCompact_Icc.prod (isCompact_closedBall 0 D))
  have hp (n : ℕ) : (h n, b n, c n) ∈
      K ×ˢ (Icc (1 / C) B ×ˢ Metric.closedBall (0 : Space) D) := by
    exact ⟨hh n, ⟨(hbbox n).1, hB n⟩,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using (hbbox n).2.2⟩
  obtain ⟨p, hpK, k, hk, hpLim⟩ := hprod.tendsto_subseq hp
  have hpPos : 0 < p.2.1 := (one_div_pos.mpr hC).trans_le hpK.2.1.1
  have hblim : Tendsto (fun n => b (k n)) atTop (𝓝 p.2.1) :=
    hpLim.snd_nhds.fst_nhds
  have hclim : Tendsto (fun n => c (k n)) atTop (𝓝 p.2.2) :=
    hpLim.snd_nhds.snd_nhds
  have hhlim : Tendsto (fun n => h (k n)) atTop (𝓝 p.1) := hpLim.fst_nhds
  have hbinv := hblim.inv₀ hpPos.ne'
  have haff := affineState_tendsto_data hSob
    (fun n => (b (k n))⁻¹) (fun n => inv_pos.mpr (hb (k n)))
    (fun n => -((b (k n))⁻¹ • c (k n))) (inv_pos.mpr hpPos)
    hbinv (hbinv.smul hclim).neg (fun n => h (k n)) hhlim
  have hglim : Tendsto (fun n => g (k n)) atTop
      (𝓝 (criticalAffineState p.2.1 hpPos p.2.2 p.1)) := by
    change Tendsto (fun n => criticalAffineState (b (k n)) (hb (k n)) (c (k n)) (h (k n)))
      atTop (𝓝 (criticalAffineState p.2.1 hpPos p.2.2 p.1)) at haff
    simpa only [heq] using haff
  exact ⟨p.1, hpK.1, p.2.1, hpPos, p.2.2, hpK.2.1.2,
    tendsto_nhds_unique (hg0.comp hk.tendsto_atTop) hglim⟩

theorem boundedAffineCarrier_mem_of_tendsto {Cs : ℝ} (hSob : OrdinarySobolev Cs)
    {K : Set EnergyState} (hK : IsCompact K) (hKzero : (0 : EnergyState) ∉ K)
    {B : ℝ} {g : ℕ → EnergyState} {g0 : EnergyState}
    (hg : Tendsto g atTop (𝓝 g0))
    (hmem : ∀ᶠ n in atTop, g n ∈ boundedAffineCarrier K B) :
    g0 ∈ boundedAffineCarrier K B :=
  (boundedAffineCarrier_isClosed hSob hK hKzero B).mem_of_tendsto hg hmem

end HartreeF.Paper121AffineClosed
