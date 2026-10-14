import FCompactPDEInputDomain
import FL1RetardedIndependentConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.HartreeDistributionalBridge
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport ForcingDomain
open LinearWeakEquation L1RetardedIndependentReview FreeDataDependence
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalPathIntervalSource extendEnergyPath

variable (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
  (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
  (q : CriticalPath (intervalMeasure a b))

/-- The actual produced Hartree L2 source embedded in L1 on the finite interval. -/
def actualHartreeSourceL1 : CompatibleL1IntervalSource a b :=
  sourceL2ToL1 (criticalPathIntervalSource hDensity hSob hH hab q 0)

theorem actualHartreeSourceL1_value_ae :
    ∀ᵐ s ∂localMeasure a b, (actualHartreeSourceL1 hDensity hSob hH hab q).value s =ᵐ[volume]
      forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ q) s)) := by
  filter_upwards [sourceL2ToL1_value (criticalPathIntervalSource hDensity hSob hH hab q 0),
    criticalPathIntervalSource_single_coeFn hDensity hSob hH hab q] with s hs hN
  simpa only [actualHartreeSourceL1, hs] using hN

/-- The produced source is the literal Hartree nonlinearity under spatial testing. -/
theorem actualHartreeSourceL1_pair_ae (φ : Test) :
    (fun s => Lp.toTemperedDistribution ((actualHartreeSourceL1 hDensity hSob hH hab q).value s) φ)
      =ᵐ[localMeasure a b]
    (fun s => ∫ x, φ x * forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ q) s)) x) := by
  filter_upwards [actualHartreeSourceL1_value_ae hDensity hSob hH hab q] with s hs
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hs] with x hx
  simp only [hx, smul_eq_mul]

/-- The original compact-test equation i q_t + Delta q + N(q) = e.
The nonlinear term is the literal Hartree spatial function, not a supplied mild identity. -/
def ForcedHartreeCompactTestIdentity (alpha c : ℝ) {a b : ℝ} (hab : a ≤ b)
    (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b) : Prop :=
  ∀ η : TimeTest, tsupport η ⊆ Set.Ioo a b → ∀ φ : Test, HasCompactSupport φ →
    (∫ s in Set.Icc a b,
      weakOperator (fun t => energyDistribution (extendEnergyPath hab (energyPath _ q) t)) η φ s) +
    (∫ s in Set.Icc a b, η s * ∫ x,
      φ x * forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ q) s)) x) =
    ∫ s in Set.Icc a b, η s * Lp.toTemperedDistribution (E.value s) φ

attribute [local irreducible] actualHartreeSourceL1
include hDensity hSob hH

/-- The literal nonlinear term has genuine time-integrable tested pairings,
derived from the actual constructed source and exact a.e. representative bridge. -/
theorem actualHartree_time_test_integrable (η : TimeTest) (φ : Test) :
    IntegrableOn (fun s => η s * ∫ x,
      φ x * forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ q) s)) x)
      (Set.Icc a b) := by
  apply (source_time_test_integrable
    (actualHartreeSourceL1 hDensity hSob hH hab q).value
    (actualHartreeSourceL1 hDensity hSob hH hab q).value_integrable η φ).congr
  exact (actualHartreeSourceL1_pair_ae hDensity hSob hH hab q φ).mono
    (fun s hs => congrArg (fun z : ℂ => η s * z) hs)

omit hDensity hSob hH in
theorem source_test_integral_sub (F G : ℝ → TD) (η : TimeTest) (φ : Test)
    (hF : IntegrableOn (fun t => η t * F t φ) (Set.Icc a b))
    (hG : IntegrableOn (fun t => η t * G t φ) (Set.Icc a b)) :
    (∫ t in Set.Icc a b, η t * (F t - G t) φ) =
      (∫ t in Set.Icc a b, η t * F t φ) - ∫ t in Set.Icc a b, η t * G t φ := by
  change (∫ t in Set.Icc a b, η t * (F t φ - G t φ)) = _
  simp_rw [mul_sub]
  exact integral_sub hF hG

/-- Subtracting the literal Hartree term yields the actual distribution source e-N(q). -/
theorem actualHartree_subtracted_PDE (E : CompatibleL1IntervalSource a b)
    (hPDE : ForcedHartreeCompactTestIdentity alpha c hab q E) :
    CompactTestIdentity a b
      (fun t => energyDistribution (extendEnergyPath hab (energyPath _ q) t))
      (fun t => Lp.toTemperedDistribution (E.value t) -
        Lp.toTemperedDistribution ((actualHartreeSourceL1 hDensity hSob hH hab q).value t)) := by
  intro η hη φ hφ
  have hE := source_time_test_integrable E.value E.value_integrable η φ
  have hN := source_time_test_integrable (actualHartreeSourceL1 hDensity hSob hH hab q).value
    (actualHartreeSourceL1 hDensity hSob hH hab q).value_integrable η φ
  have hn : (∫ s in Set.Icc a b, η s *
      Lp.toTemperedDistribution ((actualHartreeSourceL1 hDensity hSob hH hab q).value s) φ) =
      ∫ s in Set.Icc a b, η s * ∫ x,
        φ x * forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ q) s)) x :=
    integral_congr_ae ((actualHartreeSourceL1_pair_ae hDensity hSob hH hab q φ).mono
      (fun s hs => congrArg (fun z : ℂ => η s * z) hs))
  exact (eq_sub_of_add_eq (hPDE η hη φ hφ)).trans
    ((congrArg (fun z : ℂ => (∫ s in Set.Icc a b,
      η s * Lp.toTemperedDistribution (E.value s) φ) - z) hn).symm.trans
      (source_test_integral_sub (fun s => Lp.toTemperedDistribution (E.value s))
        (fun s => Lp.toTemperedDistribution
          ((actualHartreeSourceL1 hDensity hSob hH hab q).value s)) η φ hE hN).symm)

end HartreeF.HartreeDistributionalBridge
