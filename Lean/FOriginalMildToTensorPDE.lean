import FActualMildToForcedCompactPDE
import FActualTensorIntervalCompatibility

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set Laplacian
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.HartreeMildPDEProducer
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport ForcingDomain
open LinearWeakEquation L1RetardedIndependentReview HartreeDistributionalBridge CriticalUniqueness
open CompactPDEDualBridge
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  criticalPathIntervalSource intervalRetardedCriticalPath freeCriticalPath freeEnergyState
  hartreeDuhamelMap CompatibleL1IntervalSource.retardedCriticalPath actualRetardedCandidate
  extendEnergyPath

/-- The existing zero error graph has a genuinely zero tested integral; this uses
its actual a.e. quotient representative rather than an unjustified pointwise choice. -/
theorem actual_zeroSource_test_integral (a b : ℝ) (η : TimeTest) (φ : Test) :
    (∫ s in Icc a b, η s * Lp.toTemperedDistribution ((zeroSource a b).value s) φ) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero SourceSpace 1 (localMeasure a b)] with s hs
  change η s * Lp.toTemperedDistribution ((0 : Lp SourceSpace 1 (localMeasure a b)) s) φ = 0
  rw [hs]
  simp only [Pi.zero_apply]
  have hz : Lp.toTemperedDistribution (0 : SourceSpace) = (0 : TD) :=
    map_zero (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) (ENNReal.ofReal (6/5 : ℝ)))
  rw [hz]
  exact mul_zero _

variable (hDensity : OrdinaryH1Density) {K alpha c a b C0 Ch Cr : ℝ}
  (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr) (hab : a ≤ b)
  (q : CriticalPath (intervalMeasure a b)) (g : EnergyState)

include hDensity hSob hH h0 hfree hret in
/-- The literal original mild path supplies the exact previously accepted interval
compact-Hartree PDE contract. That contract is a conclusion here. -/
theorem actual_mildPath_intervalPDE
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hmild : IsMildHartreePath hab alpha c g q) :
    IntervalCompactHartreePDE alpha c (extendEnergyPath hab (energyPath _ q)) a b := by
  intro η hη φ hφ
  exact (actual_zero_compactPDE_of_original_mild
    hDensity hSob hH h0 hfree hret hab q g hgen hmild η hη φ hφ).trans
      (actual_zeroSource_test_integral a b η φ)

/-- Literal pointwise agreement of the old CriticalPath on the CLOSED interval
identifies its extension with the same original EnergyState at every interval time. -/
theorem original_state_eq_extended_path
    (u : ℝ → EnergyState) (hSame : ∀ t : Icc a b, energyPath _ q t = u t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    u t = extendEnergyPath hab (energyPath _ q) t :=
  (hSame ⟨t, ht⟩).symm.trans (extendEnergyPath_val hab (energyPath _ q) ⟨t, ht⟩).symm

include hDensity hSob hH h0 hfree hret in
/-- The equation is transported through actual original-state equality inside both
literal integrals, including the original forcing, rather than a new same-PDE premise. -/
theorem actual_original_intervalPDE_of_mild
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (u : ℝ → EnergyState) (hSame : ∀ t : Icc a b, energyPath _ q t = u t)
    (hmild : IsMildHartreePath hab alpha c g q) :
    IntervalCompactHartreePDE alpha c u a b := by
  intro η hη φ hφ
  have hp := actual_mildPath_intervalPDE hDensity hSob hH h0 hfree hret hab q g hgen hmild
    η hη φ hφ
  have hleft :
      (∫ s in Icc a b, -Complex.I * deriv η s * energyDistribution (u s) φ +
        η s * energyDistribution (u s) (Δ φ)) =
      ∫ s in Icc a b, -Complex.I * deriv η s *
        energyDistribution (extendEnergyPath hab (energyPath _ q) s) φ +
        η s * energyDistribution (extendEnergyPath hab (energyPath _ q) s)
          (Δ φ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact congrArg (fun v : EnergyState => -Complex.I * deriv η s * energyDistribution v φ +
      η s * energyDistribution v (Δ φ))
      (original_state_eq_extended_path hab q u hSame hs)
  have hright :
      (∫ s in Icc a b, η s * ∫ x : V, φ x * forcing alpha c (energyValue (u s)) x) =
      ∫ s in Icc a b, η s * ∫ x : V, φ x *
        forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ q) s)) x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact congrArg (fun v : EnergyState => η s * ∫ x : V,
      φ x * forcing alpha c (energyValue v) x)
      (original_state_eq_extended_path hab q u hSame hs)
  exact (congrArg₂ (fun x y : ℂ => x+y) hleft hright).trans hp

include hDensity hSob hH h0 hfree hret in
/-- A genuine producer of the existing open-domain CompactHartreeTensorPDE for the
same original state. The original literal mild formula, ordinary linear/HLS interfaces
and the actual closed-interval path identification are the only displayed inputs. -/
theorem actual_original_tensorPDE_of_mild
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (u : ℝ → EnergyState) (hSame : ∀ t : Icc a b, energyPath _ q t = u t)
    (hmild : IsMildHartreePath hab alpha c g q) :
    CompactHartreeTensorPDE hH u (Ioo a b) := by
  have hu : ContinuousOn u (Ioo a b) :=
    (extendEnergyPath hab (energyPath _ q)).continuous.continuousOn.congr
      (fun t ht => original_state_eq_extended_path hab q u hSame (Ioo_subset_Icc_self ht))
  exact intervalPDE_to_openTensorPDE hH hu
    (actual_original_intervalPDE_of_mild hDensity hSob hH h0 hfree hret hab q g hgen u hSame hmild)

end HartreeF.HartreeMildPDEProducer
