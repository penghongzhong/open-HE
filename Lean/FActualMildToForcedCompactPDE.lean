import FActualHartreePDEToMild
import FMildHartreeDefinition

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.HartreeMildPDEProducer
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport ForcingDomain
open LinearWeakEquation L1RetardedIndependentReview HartreeDistributionalBridge CriticalUniqueness
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution criticalPathIntervalSource intervalRetardedCriticalPath
  freeCriticalPath freeEnergyState hartreeDuhamelMap
  CompatibleL1IntervalSource.retardedCriticalPath actualRetardedCandidate extendEnergyPath

variable (hDensity : OrdinaryH1Density) {K alpha c a b C0 Ch Cr : ℝ}
  (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr) (hab : a ≤ b)
  (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
  (g : EnergyState)

/-- The actual total-source candidate is the same original energy path on the closed
interval when the genuine forced mild equality holds. No PDE is an input. -/
theorem actual_candidate_eq_original_of_forced_mild
    (hmild : q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
      Complex.I • E.retardedCriticalPath hDensity hSob h0 hret)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    actualRetardedCandidate hDensity hSob h0 hret hab
      (totalHartreeSource hDensity hSob hH hab q E) g t =
      extendEnergyPath hab (energyPath _ q) t := by
  have he := totalHartreeCandidate_energy hDensity hSob hH hab q E h0 hfree hret g ⟨t, ht⟩
  rw [← hmild] at he
  exact he.trans (extendEnergyPath_val hab (energyPath _ q) ⟨t, ht⟩).symm

/-- Actual mild-to-weak-Hartree production: the generic retarded weak PDE and the
literal source subtraction yield the original compact-test equation. No homogeneous
uniqueness, candidate PDE, mass derivative or local-charge identity is assumed. -/
theorem actual_forced_compactPDE_of_mild
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hmild : q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
      Complex.I • E.retardedCriticalPath hDensity hSob h0 hret) :
    ForcedHartreeCompactTestIdentity alpha c hab q E := by
  intro η hη φ _
  let F := totalHartreeSource hDensity hSob hH hab q E
  have hp := actualRetardedCandidate_weakEquation hDensity hSob h0 hret hab F g hgen η hη φ
  have hleft :
      (∫ s in Set.Icc a b, weakOperator
        (fun t => energyDistribution (extendEnergyPath hab (energyPath _ q) t)) η φ s) =
      ∫ s in Set.Icc a b, weakOperator
        (fun t => energyDistribution (actualRetardedCandidate hDensity hSob h0 hret hab F g t))
          η φ s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have he := actual_candidate_eq_original_of_forced_mild
      hDensity hSob hH h0 hfree hret hab q E g hmild s hs
    change _ = weakOperator
      (fun t => energyDistribution (actualRetardedCandidate hDensity hSob h0 hret hab
        (totalHartreeSource hDensity hSob hH hab q E) g t)) η φ s
    simp only [weakOperator, he]
  have hE := source_time_test_integrable E.value E.value_integrable η φ
  have hN := source_time_test_integrable
    (actualHartreeSourceL1 hDensity hSob hH hab q).value
    (actualHartreeSourceL1 hDensity hSob hH hab q).value_integrable η φ
  have htotal : (∫ s in Set.Icc a b, η s * Lp.toTemperedDistribution (F.value s) φ) =
      (∫ s in Set.Icc a b, η s * Lp.toTemperedDistribution (E.value s) φ) -
      ∫ s in Set.Icc a b, η s *
        Lp.toTemperedDistribution ((actualHartreeSourceL1 hDensity hSob hH hab q).value s) φ := by
    calc
      _ = ∫ s in Set.Icc a b, η s *
          (Lp.toTemperedDistribution (E.value s) -
            Lp.toTemperedDistribution ((actualHartreeSourceL1 hDensity hSob hH hab q).value s)) φ := by
        apply integral_congr_ae
        filter_upwards [E.sub_distribution_ae (actualHartreeSourceL1 hDensity hSob hH hab q)]
          with s hs
        change η s * Lp.toTemperedDistribution
          ((E.sub (actualHartreeSourceL1 hDensity hSob hH hab q)).value s) φ = _
        rw [hs]
      _ = _ := source_test_integral_sub _ _ η φ hE hN
  have hactual :
      (∫ s in Set.Icc a b, η s *
        Lp.toTemperedDistribution ((actualHartreeSourceL1 hDensity hSob hH hab q).value s) φ) =
      ∫ s in Set.Icc a b, η s * ∫ x,
        φ x * forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ q) s)) x :=
    integral_congr_ae ((actualHartreeSourceL1_pair_ae hDensity hSob hH hab q φ).mono
      (fun s hs => congrArg (fun z : ℂ => η s * z) hs))
  rw [hactual] at htotal
  exact eq_sub_iff_add_eq.mp (hleft.trans (hp.2.2.trans htotal))

include hDensity hSob hH h0 hfree hret in
/-- Starting with the historical literal zero-error mild equation itself produces
its original zero-error ForcedHartreeCompactTestIdentity. The source is the existing
actual zero L1 graph, not a new error/source premise. -/
theorem actual_zero_compactPDE_of_original_mild
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hmild : IsMildHartreePath hab alpha c g q) :
    ForcedHartreeCompactTestIdentity alpha c hab q (zeroSource a b) := by
  have hfixed := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    hab g q).mp hmild
  have hz : (zeroSource a b).retardedCriticalPath hDensity hSob h0 hret =
      (0 : CriticalPath (intervalMeasure a b)) :=
    zero_source_output hDensity hSob h0 hret
  have hzI : Complex.I • (zeroSource a b).retardedCriticalPath hDensity hSob h0 hret =
      (0 : CriticalPath (intervalMeasure a b)) :=
    (congrArg (fun p : CriticalPath (intervalMeasure a b) => Complex.I • p) hz).trans
      ((FreeDataDependence.canonicalPathNormedSpace a b).toModule.toDistribMulAction.smul_zero
        Complex.I)
  have he : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
      Complex.I • (zeroSource a b).retardedCriticalPath hDensity hSob h0 hret =
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q :=
    (congrArg (fun p : CriticalPath (intervalMeasure a b) =>
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q - p) hzI).trans
      (sub_zero (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q))
  exact actual_forced_compactPDE_of_mild hDensity hSob hH h0 hfree hret hab q
    (zeroSource a b) g hgen (hfixed.symm.trans he.symm)

end HartreeF.HartreeMildPDEProducer
