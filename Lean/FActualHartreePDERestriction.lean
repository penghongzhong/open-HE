import FCompactTestLocalization
import FActualHartreePDEToMild
import FHartreeSubintervalFixedPoint
import FL1SourceRestriction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.HartreeDistributionalBridge
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport ForcingDomain
open LinearWeakEquation L1RetardedIndependentReview FreeDataDependence CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  criticalGradient restrictPath extendEnergyPath hartreeDuhamelMap

/-- The original literal compact Hartree equation restricts to the same actual
trajectory and the actual restricted scalar-L1 / gradient-L2 error. -/
theorem ForcedHartreeCompactTestIdentity.restrict
    {alpha kernel a b c d : ℝ} (hab : a ≤ b)
    (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
    (hPDE : ForcedHartreeCompactTestIdentity alpha kernel hab q E)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    ForcedHartreeCompactTestIdentity alpha kernel hcd (restrictPath hac hcd hdb q)
      (E.restrict hac hdb) := by
  intro η hη φ hφ
  let Q := extendEnergyPath hab (energyPath _ q)
  let Qr := extendEnergyPath hcd (energyPath _ (restrictPath hac hcd hdb q))
  have hQ (s : ℝ) (hs : s ∈ Set.Icc c d) : Qr s = Q s :=
    extend_restrictPath_eq hac hcd hdb q hs
  have hweak : (∫ s in Set.Icc c d,
      weakOperator (fun t => energyDistribution (Qr t)) η φ s) =
      ∫ s in Set.Icc a b, weakOperator (fun t => energyDistribution (Q t)) η φ s := by
    apply Eq.trans _ (weakOperator_integral_restrict hac hdb (fun t => energyDistribution (Q t)) η hη φ).symm
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [weakOperator, hQ s hs]
  have hnonlinear : (∫ s in Set.Icc c d, η s * ∫ x,
      φ x * forcing alpha kernel (energyValue (Qr s)) x) =
      ∫ s in Set.Icc a b, η s * ∫ x,
        φ x * forcing alpha kernel (energyValue (Q s)) x := by
    apply Eq.trans _ (timeTest_mul_integral_restrict hac hdb η hη
      (fun s => ∫ x, φ x * forcing alpha kernel (energyValue (Q s)) x)).symm
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact congrArg (fun g : EnergyState => η s * ∫ x,
      φ x * forcing alpha kernel (energyValue g) x) (hQ s hs)
  have herror : (∫ s in Set.Icc a b, η s * Lp.toTemperedDistribution (E.value s) φ) =
      ∫ s in Set.Icc c d, η s * Lp.toTemperedDistribution ((E.restrict hac hdb).value s) φ := by
    apply (timeTest_mul_integral_restrict hac hdb η hη
      (fun s => Lp.toTemperedDistribution (E.value s) φ)).trans
    apply integral_congr_ae
    exact (E.restrict_value_coeFn hac hdb).mono
      (fun s hs => congrArg (fun v : SourceSpace => η s * Lp.toTemperedDistribution v φ) hs.symm)
  have hη' : tsupport η ⊆ Set.Ioo a b := fun s hs =>
    ⟨hac.trans_lt (hη hs).1, (hη hs).2.trans_le hdb⟩
  exact (congrArg₂ (fun x y : ℂ => x+y) hweak hnonlinear).trans
    ((hPDE η hη' φ hφ).trans herror)

/-- Every actual subinterval gets its self-anchored forced identity directly
from the global distributional PDE; no per-piece mild premise is introduced. -/
theorem actual_restricted_forced_mild_of_distributional
    (hDensity : OrdinaryH1Density) {K C0 Ch Cr alpha kernel a b c d : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha kernel) (hab : a ≤ b)
    (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hPDE : ForcedHartreeCompactTestIdentity alpha kernel hab q E)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    restrictPath hac hcd hdb q =
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd
        (energyPath _ q ⟨c, hac, hcd.trans hdb⟩) (restrictPath hac hcd hdb q) -
      Complex.I • (E.restrict hac hdb).retardedCriticalPath hDensity hSob h0 hret := by
  have he := actual_forced_mild_of_distributional hDensity hSob hH hcd
    (restrictPath hac hcd hdb q) (E.restrict hac hdb) h0 hfree hret hgen hUnique
    (ForcedHartreeCompactTestIdentity.restrict hab q E hPDE hac hcd hdb)
  exact he.trans (congrArg (fun g : EnergyState =>
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd g (restrictPath hac hcd hdb q) -
      Complex.I • (E.restrict hac hdb).retardedCriticalPath hDensity hSob h0 hret)
    (restrictPath_initial hac hcd hdb q))

end HartreeF.HartreeDistributionalBridge
