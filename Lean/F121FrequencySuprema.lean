import F121FrequencyOrbit

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121FrequencyOrbit
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open CriticalAffine Paper121SmallFrequency Paper121CutoffMaps

def orbitGradientSup {ι : Type*} (U : ι → EnergyState) : ℝ :=
  sSup (range (fun s => pureGradientNorm (U s)))

def orbitLowSup (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    (q : Cutoff) {ι : Type*} (U : ι → EnergyState) (M : ℝ) : ℝ :=
  if hM : 0 < M then sSup (range (fun s => pureGradientNorm (lowEnergyCLM hD hS q hM (U s)))) else 0

def orbitMassSup (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    (q : Cutoff) {ι : Type*} (U : ι → EnergyState) (M : ℝ) : ℝ :=
  if hM : 0 < M then sSup (range (fun s => ‖highValueL2CLM hD hS q hM (U s)‖)) else 0

theorem gradient_le_sup {ι : Type*} (U : ι → EnergyState)
    (hb : BddAbove (range (fun s => pureGradientNorm (U s)))) (s : ι) :
    pureGradientNorm (U s) ≤ orbitGradientSup U := le_csSup hb (mem_range_self s)

theorem orbit_cutoff_ranges_bounded (hD : OrdinaryH1Density) {K : ℝ}
    (hS : OrdinarySobolev K) (q : Cutoff) {ι : Type*} (U : ι → EnergyState)
    (hb : BddAbove (range (fun s => pureGradientNorm (U s)))) {M : ℝ} (hM : 0 < M) :
    BddAbove (range (fun s => pureGradientNorm (lowEnergyCLM hD hS q hM (U s)))) ∧
    BddAbove (range (fun s => ‖highValueL2CLM hD hS q hM (U s)‖)) := by
  constructor
  · refine ⟨orbitGradientSup U, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (low_gradient_bound hD hS q hM (U s)).trans (gradient_le_sup U hb s)
  · refine ⟨M⁻¹*orbitGradientSup U, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (highValueL2_bound hD hS q hM (U s)).trans
      (mul_le_mul_of_nonneg_left (gradient_le_sup U hb s) (inv_nonneg.mpr hM.le))

theorem orbit_mass_sup_bound (hD : OrdinaryH1Density) {K : ℝ}
    (hS : OrdinarySobolev K) (q : Cutoff) {ι : Type*} [Nonempty ι] (U : ι → EnergyState)
    (hb : BddAbove (range (fun s => pureGradientNorm (U s)))) {M : ℝ} (hM : 0 < M) :
    orbitMassSup hD hS q U M ≤ orbitGradientSup U/M := by
  rw [orbitMassSup, dif_pos hM]
  apply csSup_le (range_nonempty _)
  rintro _ ⟨s, rfl⟩
  calc
    _ ≤ M⁻¹*pureGradientNorm (U s) := highValueL2_bound hD hS q hM (U s)
    _ ≤ M⁻¹*orbitGradientSup U :=
      mul_le_mul_of_nonneg_left (gradient_le_sup U hb s) (inv_nonneg.mpr hM.le)
    _ = _ := by ring

theorem orbit_sup_nonneg (hD : OrdinaryH1Density) {K : ℝ}
    (hS : OrdinarySobolev K) (q : Cutoff) {ι : Type*} [Nonempty ι] (U : ι → EnergyState)
    (hb : BddAbove (range (fun s => pureGradientNorm (U s)))) {M : ℝ} (hM : 0 < M) :
    0 ≤ orbitLowSup hD hS q U M ∧ 0 ≤ M*orbitMassSup hD hS q U M := by
  obtain ⟨s⟩ := ‹Nonempty ι›
  have hc := orbit_cutoff_ranges_bounded hD hS q U hb hM
  simp only [orbitLowSup, orbitMassSup, dif_pos hM]
  constructor
  · exact (pureGradientNorm_nonneg _).trans (le_csSup hc.1 (mem_range_self s))
  · exact mul_nonneg hM.le ((norm_nonneg _).trans (le_csSup hc.2 (mem_range_self s)))

theorem orbit_sup_small_pair (hD : OrdinaryH1Density) {K : ℝ}
    (hS : OrdinarySobolev K) (q : Cutoff) {ι : Type*} [Nonempty ι] (U : ι → EnergyState)
    (r : ι → ℝ) (hr : ∀ s, 0 < r s) (hr1 : ∀ s, r s ≤ 1) (y : ι → Space)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hq : ∀ s, (criticalAffineState (r s) (hr s) (y s)).symm (U s) ∈ Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (M : ℝ), 0 < M → M ≤ δ →
      orbitLowSup hD hS q U M < ε ∧ M*orbitMassSup hD hS q U M < ε := by
  obtain ⟨δ, hδ, hs⟩ := normalized_orbit_small_pair hD hS q U r hr hr1 y hQ hq (half_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro M hM hMδ
  have hl : orbitLowSup hD hS q U M ≤ ε/2 := by
    rw [orbitLowSup, dif_pos hM]
    apply csSup_le (range_nonempty _)
    rintro _ ⟨s, rfl⟩
    exact (hs M hM hMδ s).1.le
  have hm : orbitMassSup hD hS q U M ≤ (ε/2)/M := by
    rw [orbitMassSup, dif_pos hM]
    apply csSup_le (range_nonempty _)
    rintro _ ⟨s, rfl⟩
    apply (le_div_iff₀ hM).mpr
    simpa only [mul_comm] using (hs M hM hMδ s).2.le
  have hw := mul_le_mul_of_nonneg_left hm hM.le
  have he : M*((ε/2)/M) = ε/2 := by field_simp
  rw [he] at hw
  exact ⟨hl.trans_lt (half_lt_self hε), hw.trans_lt (half_lt_self hε)⟩

theorem orbit_frequency_limits (hD : OrdinaryH1Density) {K : ℝ}
    (hS : OrdinarySobolev K) (q : Cutoff) {ι : Type*} [Nonempty ι] (U : ι → EnergyState)
    (r : ι → ℝ) (hr : ∀ s, 0 < r s) (hr1 : ∀ s, r s ≤ 1) (y : ι → Space)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hq : ∀ s, (criticalAffineState (r s) (hr s) (y s)).symm (U s) ∈ Q) :
    Tendsto (orbitLowSup hD hS q U) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun M => M*orbitMassSup hD hS q U M) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hb := normalized_orbit_gradient_bddAbove U r hr y hQ hq
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hs⟩ := orbit_sup_small_pair hD hS q U r hr hr1 y hQ hq hε
    have hnear : ∀ᶠ M : ℝ in 𝓝[>] (0 : ℝ), M < δ := nhdsWithin_le_nhds (gt_mem_nhds hδ)
    filter_upwards [self_mem_nhdsWithin, hnear] with M hM hlt
    simpa only [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (orbit_sup_nonneg hD hS q U hb hM).1] using (hs M hM hlt.le).1
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hs⟩ := orbit_sup_small_pair hD hS q U r hr hr1 y hQ hq hε
    have hnear : ∀ᶠ M : ℝ in 𝓝[>] (0 : ℝ), M < δ := nhdsWithin_le_nhds (gt_mem_nhds hδ)
    filter_upwards [self_mem_nhdsWithin, hnear] with M hM hlt
    simpa only [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (orbit_sup_nonneg hD hS q U hb hM).2] using (hs M hM hlt.le).2

end HartreeF.Paper121FrequencyOrbit
