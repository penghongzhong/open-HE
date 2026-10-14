import FIndependentPureGlobalConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IndependentGlobalNormBridge
open EnergySpace CriticalPathSpace ActualDuhamelPath ActualPerturbation MaximalTrajectory
open CriticalSourceBounds SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
open HomogeneousStability IntervalNormExhaustion EssentialEnergyCap TimeHolder
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  ActualNestedLpBound ActualPaperRealization actualPaperDifferenceSize

/-- On a nondegenerate interval every time is an endpoint of a positive compact
subinterval. Thus actual local essential caps bound the original state at every
time. No estimate on a measure-zero singleton is promoted to a pointwise cap. -/
theorem pure_cap_of_positive_compact_caps {B : ℝ} (hB : 0 ≤ B)
    (I : Set ℝ) (hI : OrdConnected I)
    (hne : ∃ l ∈ I, ∃ r ∈ I, l < r)
    (q : ℝ → EnergyState)
    (Q : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CriticalPath (intervalMeasure a b))
    (hQ : ∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) (t : Icc a b),
      energyPath _ (Q hab hsub) t = q t)
    (hcap : ∀ {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ I),
      mixedNorm (intervalMeasure a b) volume ∞ 2
        (fun t => energyComplexGradient (energyPath _ (Q hab.le hsub) t)) ≤ ENNReal.ofReal B) :
    ∀ t ∈ I, pureGradientNorm (q t) ≤ B := by
  obtain ⟨l,hl,r,hr,hlr⟩ := hne
  intro t ht
  by_cases htr : t < r
  · have hsub : Icc t r ⊆ I := hI.out' ht hr
    have bound := pureGradient_cap_of_actual_energy_cap htr hB (Q htr.le hsub)
      (hcap htr hsub) ⟨t,le_rfl,htr.le⟩
    rwa [hQ htr.le hsub] at bound
  · have hlt : l < t := hlr.trans_le (le_of_not_gt htr)
    have hsub : Icc l t ⊆ I := hI.out' hl ht
    have bound := pureGradient_cap_of_actual_energy_cap hlt hB (Q hlt.le hsub)
      (hcap hlt hsub) ⟨t,hlt.le,le_rfl⟩
    rwa [hQ hlt.le hsub] at bound

/-- Essential-input whole-interval stability for all nondegenerate connected
intervals, bounded or unbounded and with any endpoint inclusion. The uniform
constants are chosen before I and its local families. Singleton intervals remain
covered by the preceding pointwise-pure-input theorem. -/
theorem exists_essential_input_global_stability (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < C ∧
      ∀ (I : Set ℝ) (_hconn : OrdConnected I) (_hne : ∃ l ∈ I, ∃ r ∈ I, l < r)
      {s epsilon : ℝ} (_hsI : s ∈ I),
      ∀ (f : EnergyState) (q : ℝ → EnergyState)
      (Q : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CriticalPath (intervalMeasure a b))
      (E : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CompatibleL1IntervalSource a b),
      (∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) (t : Icc a b),
        energyPath _ (Q hab hsub) t = q t) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I),
        ForcedHartreeCompactTestIdentity alpha kernel hab (Q hab hsub) (E hab hsub)) →
      (∀ {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ I),
        mixedNorm (intervalMeasure a b) volume ∞ 2
          (fun t => energyComplexGradient (energyPath _ (Q hab.le hsub) t)) ≤ ENNReal.ofReal B) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I),
        mixedNorm (intervalMeasure a b) volume 10 10
          (fun t => energyValue (energyPath _ (Q hab hsub) t)) ≤ ENNReal.ofReal M) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I),
        (E hab hsub).paperForcingSize ≤ ENNReal.ofReal epsilon) →
      0 ≤ epsilon → epsilon ≤ epsilon0 → pureGradientNorm (f-q s) ≤ epsilon →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
      I ⊆ U.domain ∧
      ActualPaperRealization I (fun t => U.state t-q t) (C*epsilon) ∧
      actualPaperDifferenceSize I U.state q ≤ ENNReal.ofReal (C*epsilon) ∧
      ∀ t ∈ I, pureGradientNorm (U.state t-q t) ≤ C*epsilon := by
  let result := exists_pure_input_global_stability
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB hM
  let epsilon0 : ℝ := Classical.choose result
  let constants := Classical.choose_spec result
  let C : ℝ := Classical.choose constants
  have hc := Classical.choose_spec constants
  refine ⟨epsilon0,C,hc.1,hc.2.1,hc.2.2.1,?_⟩
  intro I hI hne s epsilon hs f q Q E hQ hPDE hE hS herr heps hsm hf
  exact hc.2.2.2 I hI hs f q Q E hQ hPDE
    (pure_cap_of_positive_compact_caps hB I hI hne q Q hQ hE) hS herr heps hsm hf

#print axioms pure_cap_of_positive_compact_caps
#print axioms exists_essential_input_global_stability
end HartreeF.IndependentGlobalNormBridge
