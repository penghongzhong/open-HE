import FRawCriticalPathProducer
import FRawL1GradientSource
import FActualEuclideanForcingNorm
import FActualHartreeCompactPDE
import FCompactTestLocalization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.RawStabilityInputs
open EnergySpace CriticalPathSpace TimeHolder CriticalPathRestriction HomogeneousStability
open SobolevStretch StationarySelfTest EndpointOutput ActualDuhamelPath IntervalTimeTransport Retarded
open HartreeDistributionalBridge LinearWeakEquation ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  LocallyCriticalEnergyCurve.compactPath RawSpatialGradientSource.compactSource

/-- Literal distributional testing of the single raw q and e on I. Compact
support in an interior compact interval is used only to express locality. -/
def RawHartreeTestIdentity (alpha kernel : ℝ) (I : Set ℝ)
    (q : ℝ → EnergyState) (e : ℝ → Space → ℂ) : Prop :=
  ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I →
    ∀ η : TimeTest, tsupport η ⊆ Ioo a b → ∀ φ : Test, HasCompactSupport φ →
      (∫ s in I, weakOperator (fun t => energyDistribution (q t)) η φ s) +
      (∫ s in I, η s * ∫ x, φ x * forcing alpha kernel (energyValue (q s)) x) =
      ∫ s in I, η s * ∫ x, φ x * e s x

/-- Arbitrary-interval localization of the literal time test, without any
extension or regularity assumption outside I. -/
theorem raw_time_pairing_restrict {I : Set ℝ} {a b : ℝ} (hmeas : MeasurableSet I) (hI : Icc a b ⊆ I)
    (η : TimeTest) (hη : tsupport η ⊆ Ioo a b) (g : ℝ → ℂ) :
    (∫ s in I, η s * g s) = ∫ s in Icc a b, η s * g s := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hI
  intro s hs
  rw [(timeTest_zero_outside η hη hs.2).1, zero_mul]

theorem raw_weakOperator_restrict {I : Set ℝ} {a b : ℝ} (hmeas : MeasurableSet I) (hI : Icc a b ⊆ I)
    (η : TimeTest) (hη : tsupport η ⊆ Ioo a b) (φ : Test) (q : ℝ → EnergyState) :
    (∫ s in I, weakOperator (fun t => energyDistribution (q t)) η φ s) =
      ∫ s in Icc a b, weakOperator (fun t => energyDistribution (q t)) η φ s := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hI
  intro s hs
  have hz := timeTest_zero_outside η hη hs.2
  simp only [weakOperator, hz.1, hz.2, mul_zero, zero_mul, add_zero]

/-- The produced compact source represents exactly the original scalar error
under every spatial Schwartz test. -/
theorem RawSpatialGradientSource.compactSource_pair_ae
    {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (h : RawSpatialGradientSource I e G) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I)
    (φ : Test) :
    (fun t => Lp.toTemperedDistribution ((h.compactSource hab hI).value t) φ)
      =ᵐ[localMeasure a b] (fun t => ∫ x, φ x * e t x) := by
  filter_upwards [h.compactSource_value_ae hab hI] with t ht
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  simp only [hx, smul_eq_mul]

/-- The compact equation is produced from the original raw distributional
identity. Every occurrence of the state and error is identified explicitly. -/
theorem compactPDE_of_raw {alpha kernel : ℝ} {I : Set ℝ}
    {q : ℝ → EnergyState} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (hmeas : MeasurableSet I)
    (hq : LocallyCriticalEnergyCurve I q) (he : RawSpatialGradientSource I e G)
    (hPDE : RawHartreeTestIdentity alpha kernel I q e)
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    ForcedHartreeCompactTestIdentity alpha kernel hab (hq.compactPath hab hI)
      (he.compactSource hab hI) := by
  intro η hη φ hφ
  have hqeq (t : ℝ) (ht : t ∈ Icc a b) :
      extendEnergyPath hab (energyPath _ (hq.compactPath hab hI)) t = q t := by
    exact (extendEnergyPath_val hab (energyPath _ (hq.compactPath hab hI)) ⟨t,ht⟩).trans
      (hq.compactPath_energy hab hI ⟨t,ht⟩)
  have hweak : (∫ s in Icc a b, weakOperator
      (fun t => energyDistribution (extendEnergyPath hab (energyPath _ (hq.compactPath hab hI)) t))
      η φ s) = ∫ s in I, weakOperator (fun t => energyDistribution (q t)) η φ s := by
    apply Eq.trans _ (raw_weakOperator_restrict hmeas hI η hη φ q).symm
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [weakOperator, hqeq s hs]
  have hforce : (∫ s in Icc a b, η s * ∫ x,
      φ x * forcing alpha kernel (energyValue
        (extendEnergyPath hab (energyPath _ (hq.compactPath hab hI)) s)) x) =
      ∫ s in I, η s * ∫ x, φ x * forcing alpha kernel (energyValue (q s)) x := by
    apply Eq.trans _ (raw_time_pairing_restrict hmeas hI η hη
      (fun s => ∫ x, φ x * forcing alpha kernel (energyValue (q s)) x)).symm
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact congrArg (fun g : EnergyState => η s * ∫ x,
      φ x * forcing alpha kernel (energyValue g) x) (hqeq s hs)
  have herr : (∫ s in I, η s * ∫ x, φ x * e s x) =
      ∫ s in Icc a b, η s * Lp.toTemperedDistribution ((he.compactSource hab hI).value s) φ := by
    apply (raw_time_pairing_restrict hmeas hI η hη (fun s => ∫ x, φ x * e s x)).trans
    apply integral_congr_ae
    exact (he.compactSource_pair_ae hab hI φ).mono
      (fun s hs => congrArg (fun z : ℂ => η s * z) hs.symm)
  exact (congrArg₂ (fun x y : ℂ => x+y) hweak hforce).trans
    ((hPDE hab hI η hη φ hφ).trans herr)

/-- Compact Euclidean forcing size equals the norm of the original raw vector,
so the global actual N bound restricts with constant one. -/
theorem RawSpatialGradientSource.compactSource_paperForcingSize
    {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (h : RawSpatialGradientSource I e G) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    (h.compactSource hab hI).paperForcingSize =
      mixedNorm (localMeasure a b) volume 2 sourceExponent G := by
  apply eLpNorm_congr_ae
  filter_upwards [h.compactSource_vector_ae hab hI] with t ht
  exact eLpNorm_congr_ae ht

theorem RawSpatialGradientSource.compactSource_paperForcingSize_le
    {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (h : RawSpatialGradientSource I e G) {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    (h.compactSource hab hI).paperForcingSize ≤
      mixedNorm (volume.restrict I) volume 2 sourceExponent G := by
  rw [h.compactSource_paperForcingSize hab hI]
  exact eLpNorm_mono_measure _ (RawSpatialGradientSource.localMeasure_le hI)

/-- Restriction of the produced scalar source is norm-contracting. -/
theorem RawSpatialGradientSource.compactSource_value_norm_mono
    {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (h : RawSpatialGradientSource I e G) {a b c d : ℝ}
    (hab : a ≤ b) (hI : Icc a b ⊆ I) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    ‖(h.compactSource hcd ((Icc_subset_Icc hac hdb).trans hI)).value‖ ≤
      ‖(h.compactSource hab hI).value‖ := by
  rw [← h.compactSource_restrict hab hI hac hcd hdb]
  exact (h.compactSource hab hI).restrict_value_norm_le hac hdb

/-- The exact original Euclidean forcing norm is monotone on nested compacts. -/
theorem RawSpatialGradientSource.compactSource_paperForcingSize_mono
    {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (h : RawSpatialGradientSource I e G) {a b c d : ℝ}
    (hab : a ≤ b) (hI : Icc a b ⊆ I) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (h.compactSource hcd ((Icc_subset_Icc hac hdb).trans hI)).paperForcingSize ≤
      (h.compactSource hab hI).paperForcingSize := by
  rw [h.compactSource_paperForcingSize, h.compactSource_paperForcingSize]
  exact eLpNorm_mono_measure _ (localMeasure_mono hac hdb)

/-- Pure measure transport bounds every actual compact mixed norm by its
original norm on I; this holds for all time exponents, including infinity. -/
theorem compact_mixedNorm_le_restrict {V : Type*} [NormedAddCommGroup V]
    {I : Set ℝ} {a b : ℝ} (hI : Icc a b ⊆ I) (p r : ℝ≥0∞)
    (f : ℝ → Space → V) :
    mixedNorm (intervalMeasure a b) volume p r (fun t => f t) ≤
      mixedNorm (volume.restrict I) volume p r f := by
  have he := (MeasurableEmbedding.subtype_coe (show MeasurableSet (Icc a b) from
    measurableSet_Icc)).eLpNorm_map_measure
    (g := fun t => eLpNorm (f t) r volume) (p := p) (μ := intervalMeasure a b)
  rw [(inclusion_measurePreserving a b).map_eq] at he
  change eLpNorm ((fun t => eLpNorm (f t) r volume) ∘ Subtype.val) p (intervalMeasure a b) ≤ _
  rw [← he]
  exact eLpNorm_mono_measure _ (RawSpatialGradientSource.localMeasure_le hI)

#print axioms compactPDE_of_raw
#print axioms RawSpatialGradientSource.compactSource_paperForcingSize_le
#print axioms compact_mixedNorm_le_restrict
end HartreeF.RawStabilityInputs
