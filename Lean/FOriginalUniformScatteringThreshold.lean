import FActualCriticalThreshold

/-! Hartree v23, the uniform scattering threshold preceding Lemma 2.16.
The bound is uniform over data AND compact intervals in each native lifespan.
This differs from the existing infimum of individual bad-data energies.
We prove only the justified comparison, not equality of the two thresholds. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.OriginalUniformThreshold
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz ActualCriticalThreshold

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))

/-- A single S bound for the entire stable energy sublevel. -/
def UniformSBelow (E : ℝ) : Prop :=
  ∃ R : ℝ≥0, ∀ f : EnergyState, StableDatum alpha f → totalEnergy alpha f ≤ E →
    UniformCompactS
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f) R

def uniformEnergies : Set ℝ :=
  {E | E < totalEnergy alpha (normalizedBubbleState alpha) ∧
    UniformSBelow hDensity hSob h0 hfree hret hefree heret hOrd E}

def uniformCriticalLevel : ℝ :=
  sSup (uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd)

theorem uniformSBelow_mono {E F : ℝ} (hEF : E ≤ F)
    (hF : UniformSBelow hDensity hSob h0 hfree hret hefree heret hOrd F) :
    UniformSBelow hDensity hSob h0 hfree hret hefree heret hOrd E := by
  obtain ⟨R, hR⟩ := hF
  exact ⟨R, fun f hf he => hR f hf (he.trans hEF)⟩

theorem uniformEnergies_bddAbove :
    BddAbove (uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd) :=
  ⟨totalEnergy alpha (normalizedBubbleState alpha), fun _ hE => hE.1.le⟩

/-- A uniform sublevel cannot contain any actual bad datum. -/
theorem uniformSBelow_le_native
    (hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f)
    {E : ℝ} (hE : UniformSBelow hDensity hSob h0 hfree hret hefree heret hOrd E) :
    E ≤ criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd := by
  apply le_csInf (badEnergies_nonempty hDensity hSob h0 hfree hret hefree heret hOrd hbad)
  rintro e ⟨f, hf, hfe⟩
  by_contra hnot
  have hle : totalEnergy alpha f ≤ E := hfe.le.trans (le_of_not_ge hnot)
  obtain ⟨R, hR⟩ := hE
  exact hf.2 ⟨R, hR f hf.1 hle⟩

/-- The actual small-energy theorem supplies a positive member of the set;
no uniform lower-energy scattering estimate is assumed. -/
theorem exists_positive_uniform_energy
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    ∃ E ∈ uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd, 0 < E := by
  obtain ⟨epsilon, hepsilon, R, hseed⟩ := SmallEnergy.exists_positive_uniform_energy_seed
    hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6
  obtain ⟨hEc, hEcW⟩ := criticalLevel_pos_lt hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 hbad
  let E := min epsilon (criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd / 2)
  have hEpos : 0 < E := lt_min hepsilon (half_pos hEc)
  have hEW : E < totalEnergy alpha (normalizedBubbleState alpha) :=
    (min_le_right _ _).trans_lt ((half_lt_self hEc).trans hEcW)
  refine ⟨E, ⟨hEW, R, ?_⟩, hEpos⟩
  intro f hf he
  exact hseed (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f)
    hf.1 hf.2 (he.trans (min_le_left _ _))

/-- The original uniform threshold is positive and no larger than the native
bad-data infimum. The reverse inequality remains a separate proof obligation. -/
theorem uniformCriticalLevel_pos_le_native
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hbad : ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    0 < uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
    uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ≤
      criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd ∧
    criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd <
      totalEnergy alpha (normalizedBubbleState alpha) := by
  obtain ⟨E, hE, hEpos⟩ := exists_positive_uniform_energy hDensity hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 hbad
  have hpos := hEpos.trans_le (le_csSup
    (uniformEnergies_bddAbove hDensity hSob h0 hfree hret hefree heret hOrd) hE)
  refine ⟨hpos, csSup_le ⟨E, hE⟩ ?_,
    (criticalLevel_pos_lt hDensity hSob h0 hfree hret hefree heret hOrd
      hH hS S Bw Bs B6 hbad).2⟩
  intro e he
  exact uniformSBelow_le_native hDensity hSob h0 hfree hret hefree heret hOrd hbad he.2

/-- Below the uniform threshold there really is one common bound. -/
theorem uniformSBelow_of_lt
    (hne : (uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd).Nonempty)
    {E : ℝ} (hE : E < uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd) :
    UniformSBelow hDensity hSob h0 hfree hret hefree heret hOrd E := by
  have hupper : ∃ F ∈ uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd, E < F := by
    by_contra! hnot
    exact (not_le_of_gt hE) (csSup_le hne hnot)
  obtain ⟨F, hF, hEF⟩ := hupper
  exact uniformSBelow_mono hDensity hSob h0 hfree hret hefree heret hOrd hEF.le hF.2

/-- Above the uniform threshold, every proposed bound fails for some stable
actual datum. The witness is not falsely asserted to have infinite S. -/
theorem exists_sublevel_datum_exceeding_bound {E : ℝ}
    (hE : uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd < E)
    (hEW : E < totalEnergy alpha (normalizedBubbleState alpha)) (R : ℝ≥0) :
    ∃ f : EnergyState, StableDatum alpha f ∧ totalEnergy alpha f ≤ E ∧
      ¬ UniformCompactS
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f) R := by
  by_contra! hnot
  have hmem : E ∈ uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd :=
    ⟨hEW, R, hnot⟩
  exact (not_le_of_gt hE) (le_csSup
    (uniformEnergies_bddAbove hDensity hSob h0 hfree hret hefree heret hOrd) hmem)

end HartreeF.OriginalUniformThreshold
