import FPositiveActualWaveOperator
import FNegativeActualWaveOperator
import F121WaveCompactBounds
import F121ActualHalfLineTails
import F121WaveTrajectoryEnergy

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HartreeF.Paper121Theorem312
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath CriticalUniqueness
open EndpointOutput FreeDataDependence CriticalSourceBounds ActualPerturbation
open MaximalTrajectory IntervalNormExhaustion WaveRealization IncomingWaveRealization
open StateEnergy EnergyVariation Regularization.Actual FreeTimeDecay TimeHolder
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath actualMaximalTrajectory

/-- The three literal finite-time-exponent norms in original Theorem 3.12. -/
def waveTailSize (I : Set ℝ) (u : ℝ → EnergyState) : ℝ≥0∞ :=
  mixedNorm (volume.restrict I) volume 10 10 (fun t => energyValue (u t)) +
  mixedNorm (volume.restrict I) volume 10 CriticalPathSpace.criticalExponent
    (fun t => energyComplexGradient (u t)) +
  mixedNorm (volume.restrict I) volume 2 6 (fun t => energyComplexGradient (u t))

structure PositiveWaveConclusion (hDensity : OrdinaryH1Density)
    {K alpha T : ℝ} {f : EnergyState} (hSob : OrdinarySobolev K)
    (phi : EnergyState)
    (M : LocalMildTrajectory alpha (HeatRiesz.standardRieszConstant alpha) T f) : Prop where
  halfDomain : Ici T ⊆ M.domain
  stateCap : ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Ici T, ‖M.state t‖ ≤ B
  prescribedAsymptote : Tendsto
    (fun t => ‖M.state t-freeEnergyState hDensity hSob t phi‖) atTop (𝓝 0)
  vanishingTails : Tendsto (fun a => waveTailSize (Ici a) M.state) atTop (𝓝 0)
  energyOnEntireDomain : ∀ t ∈ M.domain, totalEnergy alpha (M.state t) = gradientSquared phi/2

structure NegativeWaveConclusion (hDensity : OrdinaryH1Density)
    {K alpha T : ℝ} {f : EnergyState} (hSob : OrdinarySobolev K)
    (phi : EnergyState)
    (M : LocalMildTrajectory alpha (HeatRiesz.standardRieszConstant alpha) T f) : Prop where
  halfDomain : Iic T ⊆ M.domain
  stateCap : ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Iic T, ‖M.state t‖ ≤ B
  prescribedAsymptote : Tendsto
    (fun t => ‖M.state t-freeEnergyState hDensity hSob t phi‖) atBot (𝓝 0)
  vanishingTails : Tendsto (fun a => waveTailSize (Iic a) M.state) atBot (𝓝 0)
  energyOnEntireDomain : ∀ t ∈ M.domain, totalEnergy alpha (M.state t) = gradientSquared phi/2

private theorem right_union (T : ℝ) : (⋃ n : ℕ, Icc T (T+n)) = Ici T := by
  ext t
  simp only [mem_iUnion,mem_Icc,mem_Ici]
  constructor
  · rintro ⟨n,ht,_⟩; exact ht
  · intro ht
    obtain ⟨n,hn⟩ := exists_nat_ge (t-T)
    exact ⟨n,ht,by linarith⟩

private theorem left_union (T : ℝ) : (⋃ n : ℕ, Icc (T-n) T) = Iic T := by
  ext t
  simp only [mem_iUnion,mem_Icc,mem_Iic]
  constructor
  · rintro ⟨n,_,ht⟩; exact ht
  · intro ht
    obtain ⟨n,hn⟩ := exists_nat_ge (T-t)
    exact ⟨n,by linarith,ht⟩

private theorem positive_tail_of_realization {T C : ℝ} {u : ℝ → EnergyState}
    (h : ActualPaperRealization (Ici T) u C) :
    Tendsto (fun a => waveTailSize (Ici a) u) atTop (𝓝 0) := by
  have hs := actualNestedLpBound_Ici_tail volume 10 10 (by norm_num) h.2.2.2
  have hw := actualNestedLpBound_Ici_tail volume 10 CriticalPathSpace.criticalExponent (by norm_num) h.2.1
  have hz := actualNestedLpBound_Ici_tail volume 2 6 (by norm_num) h.2.2.1
  simpa only [waveTailSize,add_zero] using (hs.add hw).add hz

private theorem negative_tail_of_realization {T C : ℝ} {u : ℝ → EnergyState}
    (h : ActualPaperRealization (Iic T) u C) :
    Tendsto (fun a => waveTailSize (Iic a) u) atBot (𝓝 0) := by
  have hs := actualNestedLpBound_Iic_tail volume 10 10 (by norm_num) h.2.2.2
  have hw := actualNestedLpBound_Iic_tail volume 10 CriticalPathSpace.criticalExponent (by norm_num) h.2.1
  have hz := actualNestedLpBound_Iic_tail volume 2 6 (by norm_num) h.2.2.1
  simpa only [waveTailSize,add_zero] using (hs.add hw).add hz

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
  (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
  (Bs : OrdinaryBesselLp Regularization.Actual.sourceExponent) (B6 : OrdinaryBesselLp 6)

include S Bw Bs B6 in
/-- Original outgoing wave operator, now including the same trajectory's true
S/W/Z tails and its energy on the entire maximal domain. -/
theorem theorem312_positive_wave (phi : EnergyState) :
    ∃ T : ℝ, ∃ f : EnergyState,
      PositiveWaveConclusion hDensity hSob phi
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f) := by
  obtain ⟨B,rho,T,f,hB,hrho,_hrho1,hhalf,hasymptote,hpaths⟩ :=
    exists_positive_actual_wave_operator hDensity hSob h0 hfree hret hefree heret hH phi
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
  have stateCap (t : ℝ) (ht : T ≤ t) : ‖M.state t‖ ≤ B := by
    obtain ⟨u,hu,_hm,hE,_hW⟩ := hpaths t ht
    rw [hu ⟨t,ht,le_rfl⟩]
    exact ((energyPath _ u).norm_coe_le_norm ⟨t,ht,le_rfl⟩).trans hE
  obtain ⟨C,hC,hcap⟩ := exists_compact_fullZS_cap hDensity hSob h0 hfree hret hefree heret hH hB.le hrho.le
  have hTn (n : ℕ) : T ≤ T+(n:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  choose U hU hUmild hUE hUW using fun n : ℕ => hpaths (T+n) (hTn n)
  have hmono : Monotone (fun n : ℕ => T+(n:ℝ)) := by
    intro n m hnm
    have h : (n:ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  have hd (n : ℕ) (t : Icc T (T+(n:ℝ))) :
      energyPath _ (U n-(0 : CriticalPath (intervalMeasure T (T+n)))) t = M.state t := by
    have hz : U n-(0 : CriticalPath (intervalMeasure T (T+n)))=U n := sub_zero (U n)
    rw [hz]
    exact (hU n t).symm
  have hreal := actualPaperRealization_of_compact_differences hDensity hSob hC
    (fun _ : ℕ => T) (fun n : ℕ => T+(n:ℝ)) antitone_const hmono hTn M.state U (fun _ => 0) hd
    (fun n => hcap (hTn n) f (U n) (hUmild n) (hUE n) (hUW n))
  rw [right_union] at hreal
  have htail := positive_tail_of_realization hreal
  have hseq : Tendsto (fun n : ℕ => T+(n:ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (b-T))] with n hn
    linarith
  have henergy := totalEnergy_of_actual_free_asymptote hDensity hSob h0 hfree hret hefree heret hH
    S Bw Bs B6 M phi atTop (fun n : ℕ => T+(n:ℝ)) hseq
    (fun n => hhalf (hTn n)) (fun n => stateCap _ (hTn n)) hasymptote
    (freeEnergyState_value_norm_tendsto_zero_atTop hDensity hSob hfree phi)
  exact ⟨T,f,hhalf,⟨B,hB,stateCap⟩,hasymptote,htail,henergy⟩

include S Bw Bs B6 in
/-- The incoming wave is a separate canonical trajectory; no opposite-time
global existence assertion is introduced. -/
theorem theorem312_negative_wave (phi : EnergyState) :
    ∃ T : ℝ, ∃ f : EnergyState,
      NegativeWaveConclusion hDensity hSob phi
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f) := by
  obtain ⟨B,rho,T,f,hB,hrho,_hrho1,hhalf,hasymptote,hpaths⟩ :=
    exists_negative_actual_wave_operator hDensity hSob h0 hfree hret hefree heret hH phi
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
  have stateCap (t : ℝ) (ht : t ≤ T) : ‖M.state t‖ ≤ B := by
    obtain ⟨u,hu,_hbm,_hm,hE,_hW⟩ := hpaths t ht
    rw [hu ⟨t,le_rfl,ht⟩]
    exact ((energyPath _ u).norm_coe_le_norm ⟨t,le_rfl,ht⟩).trans hE
  obtain ⟨C,hC,hcap⟩ := exists_compact_fullZS_cap hDensity hSob h0 hfree hret hefree heret hH hB.le hrho.le
  have hnT (n : ℕ) : T-(n:ℝ) ≤ T := by linarith [Nat.cast_nonneg (α := ℝ) n]
  choose U hU hUback hUmild hUE hUW using fun n : ℕ => hpaths (T-n) (hnT n)
  have hanti : Antitone (fun n : ℕ => T-(n:ℝ)) := by
    intro n m hnm
    have h : (n:ℝ) ≤ m := by exact_mod_cast hnm
    linarith
  have hd (n : ℕ) (t : Icc (T-(n:ℝ)) T) :
      energyPath _ (U n-(0 : CriticalPath (intervalMeasure (T-n) T))) t = M.state t := by
    have hz : U n-(0 : CriticalPath (intervalMeasure (T-n) T))=U n := sub_zero (U n)
    rw [hz]
    exact (hU n t).symm
  have hreal := actualPaperRealization_of_compact_differences hDensity hSob hC
    (fun n : ℕ => T-(n:ℝ)) (fun _ : ℕ => T) hanti monotone_const hnT M.state U (fun _ => 0) hd
    (fun n => hcap (hnT n) (energyPath _ (U n) ⟨T-n,le_rfl,hnT n⟩)
      (U n) (hUmild n) (hUE n) (hUW n))
  rw [left_union] at hreal
  have htail := negative_tail_of_realization hreal
  have hseq : Tendsto (fun n : ℕ => T-(n:ℝ)) atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (T-b))] with n hn
    linarith
  have henergy := totalEnergy_of_actual_free_asymptote hDensity hSob h0 hfree hret hefree heret hH
    S Bw Bs B6 M phi atBot (fun n : ℕ => T-(n:ℝ)) hseq
    (fun n => hhalf (hnT n)) (fun n => stateCap _ (hnT n)) hasymptote
    (freeEnergyState_value_norm_tendsto_zero_atBot hDensity hSob hfree phi)
  exact ⟨T,f,hhalf,⟨B,hB,stateCap⟩,hasymptote,htail,henergy⟩

include S Bw Bs B6 in
/-- Both complete original wave-operator conclusions, for arbitrary original
homogeneous data and independently chosen actual maximal trajectories. -/
theorem theorem312_both_prescribed_wave_operators (phi : EnergyState) :
    (∃ T : ℝ, ∃ f : EnergyState, PositiveWaveConclusion hDensity hSob phi
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f)) ∧
    (∃ T : ℝ, ∃ f : EnergyState, NegativeWaveConclusion hDensity hSob phi
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f)) :=
  ⟨theorem312_positive_wave hDensity hSob h0 hfree hret hefree heret hH S Bw Bs B6 phi,
   theorem312_negative_wave hDensity hSob h0 hfree hret hefree heret hH S Bw Bs B6 phi⟩

end HartreeF.Paper121Theorem312
