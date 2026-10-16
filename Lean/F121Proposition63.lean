import F121FrequencySuprema

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121FrequencyOrbit
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open CriticalAffine Paper121SmallFrequency Paper121CutoffMaps

/-- Proposition 6.3 on the SAME closed half-orbit, with arbitrary pointwise normalizers.
All suprema are of actual scalar norms; boundedness is an output, not an assumption.
The retained ordinary inputs are exactly those needed to construct the actual cutoffs. -/
theorem proposition63_halfline (hD : OrdinaryH1Density) {K : ℝ}
    (hS : OrdinarySobolev K) (q : Cutoff) (U : ℝ → EnergyState)
    (hU : ContinuousOn U (Ici 0)) (r : ℝ → ℝ) (y : ℝ → Space)
    (hr : ∀ s ∈ Ici (0 : ℝ), 0 < r s) (hr1 : ∀ s ∈ Ici (0 : ℝ), r s ≤ 1)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hq : ∀ s (hs : s ∈ Ici (0 : ℝ)),
      (criticalAffineState (r s) (hr s hs) (y s)).symm (U s) ∈ Q) :
    let V : Ici (0 : ℝ) → EnergyState := fun s => U s
    BddAbove (range (fun s => pureGradientNorm (V s))) ∧
    0 ≤ orbitGradientSup V ∧
    orbitGradientSup V ≤ sSup (pureGradientNorm '' Q) ∧
    (∀ (M : ℝ) (hM : 0 < M),
      BddAbove (range (fun s => pureGradientNorm (lowEnergyCLM hD hS q hM (V s)))) ∧
      BddAbove (range (fun s => ‖highValueL2CLM hD hS q hM (V s)‖)) ∧
      0 ≤ orbitLowSup hD hS q V M ∧ orbitLowSup hD hS q V M ≤ orbitGradientSup V ∧
      0 ≤ orbitMassSup hD hS q V M ∧ orbitMassSup hD hS q V M ≤ orbitGradientSup V/M ∧
      ContinuousOn (fun s => highH1State hD hS q hM (U s)) (Ici 0)) ∧
    Tendsto (orbitLowSup hD hS q V) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun M => M*orbitMassSup hD hS q V M) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let V : Ici (0 : ℝ) → EnergyState := fun s => U s
  let r' : Ici (0 : ℝ) → ℝ := fun s => r s
  let y' : Ici (0 : ℝ) → Space := fun s => y s
  have hr' (s : Ici (0 : ℝ)) : 0 < r' s := hr s s.property
  have hr1' (s : Ici (0 : ℝ)) : r' s ≤ 1 := hr1 s s.property
  have hq' (s : Ici (0 : ℝ)) : (criticalAffineState (r' s) (hr' s) (y' s)).symm (V s) ∈ Q :=
    hq s s.property
  letI : Nonempty (Ici (0 : ℝ)) := ⟨⟨0, by simp⟩⟩
  have hb := normalized_orbit_gradient_bddAbove V r' hr' y' hQ hq'
  have hB0 : 0 ≤ orbitGradientSup V :=
    (pureGradientNorm_nonneg (V ⟨0, by simp⟩)).trans (gradient_le_sup V hb ⟨0, by simp⟩)
  have hBQ : orbitGradientSup V ≤ sSup (pureGradientNorm '' Q) := by
    apply csSup_le (range_nonempty _)
    rintro _ ⟨s, rfl⟩
    rw [normalized_gradient_eq (r' s) (hr' s) (y' s)]
    exact le_csSup (compact_gradient_bddAbove hQ) (mem_image_of_mem _ (hq' s))
  refine ⟨hb, hB0, hBQ, ?_, orbit_frequency_limits hD hS q V r' hr' hr1' y' hQ hq'⟩
  intro M hM
  have hc := orbit_cutoff_ranges_bounded hD hS q V hb hM
  have hn := orbit_sup_nonneg hD hS q V hb hM
  have hmass0 : 0 ≤ orbitMassSup hD hS q V M := by nlinarith [hn.2]
  have hlowB : orbitLowSup hD hS q V M ≤ orbitGradientSup V := by
    rw [orbitLowSup, dite_eq_left hM]
    apply csSup_le (range_nonempty _)
    rintro _ ⟨s, rfl⟩
    exact (low_gradient_bound hD hS q hM (V s)).trans (gradient_le_sup V hb s)
  exact ⟨hc.1, hc.2, hn.1, hlowB, hmass0, orbit_mass_sup_bound hD hS q V hb hM,
    continuousOn_highpass_H1 hD hS q hM hU⟩

end HartreeF.Paper121FrequencyOrbit
