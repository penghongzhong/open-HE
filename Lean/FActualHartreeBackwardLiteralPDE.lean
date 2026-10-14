import FActualHartreePDEToMild

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.HartreeDistributionalBridge
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport ForcingDomain
open LinearWeakEquation L1RetardedIndependentReview FreeDataDependence FreeTestBounds
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  criticalGradient criticalPathIntervalSource

theorem backward_scalar_algebra (x e n : ℂ) :
    x - Complex.I * (-(e-n)) = x - Complex.I * n + Complex.I * e := by ring

variable (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
  (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
  (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)

/-- Both future integrals pair the actual original sources with the actual free test. -/
theorem actual_hartree_future_pair_integrable (t : Set.Icc a b) (φ : Test) :
    IntegrableOn (fun s => Lp.toTemperedDistribution
      ((criticalPathIntervalSource hDensity hSob hH hab q 0).value s)
      (freeTest ((t : ℝ)-s) φ)) (Set.Ioc (t : ℝ) b) ∧
    IntegrableOn (fun s => Lp.toTemperedDistribution (E.value s)
      (freeTest ((t : ℝ)-s) φ)) (Set.Ioc (t : ℝ) b) := by
  have hJ : Set.Ioc (t : ℝ) b ⊆ Set.Icc a b := fun s hs => ⟨t.property.1.trans hs.1.le, hs.2⟩
  have hN : IntegrableOn (fun s => Lp.toTemperedDistribution
      ((criticalPathIntervalSource hDensity hSob hH hab q 0).value s)
      (freeTest ((t : ℝ)-s) φ)) (Set.Icc a b) :=
    freeTestPair_integrable hDensity hSob (localMeasure a b) t φ
    (criticalPathIntervalSource hDensity hSob hH hab q 0).value
    ((Lp.memLp _).integrable (by norm_num))
  have hE : IntegrableOn (fun s => Lp.toTemperedDistribution (E.value s)
      (freeTest ((t : ℝ)-s) φ)) (Set.Icc a b) :=
    freeTestPair_integrable hDensity hSob (localMeasure a b) t φ E.value
      E.value_integrable
  exact ⟨hN.mono_set hJ, hE.mono_set hJ⟩

/-- The future total-source integral is the difference of the genuine error and Hartree integrals. -/
theorem totalHartreeSource_future_integral (t : Set.Icc a b) (φ : Test) :
    (∫ s in Set.Ioc (t : ℝ) b,
      Lp.toTemperedDistribution ((totalHartreeSource hDensity hSob hH hab q E).value s)
        (freeTest ((t : ℝ)-s) φ)) =
    (∫ s in Set.Ioc (t : ℝ) b,
      Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ)) -
    ∫ s in Set.Ioc (t : ℝ) b,
      Lp.toTemperedDistribution ((criticalPathIntervalSource hDensity hSob hH hab q 0).value s)
        (freeTest ((t : ℝ)-s) φ) := by
  have hJ : Set.Ioc (t : ℝ) b ⊆ Set.Icc a b := fun s hs => ⟨t.property.1.trans hs.1.le, hs.2⟩
  have hAE : ∀ᵐ s ∂volume.restrict (Set.Ioc (t : ℝ) b),
      Lp.toTemperedDistribution ((totalHartreeSource hDensity hSob hH hab q E).value s)
        (freeTest ((t : ℝ)-s) φ) =
      Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) -
      Lp.toTemperedDistribution ((criticalPathIntervalSource hDensity hSob hH hab q 0).value s)
        (freeTest ((t : ℝ)-s) φ) := by
    apply ae_mono (Measure.restrict_mono_set volume hJ)
    filter_upwards [E.sub_distribution_ae (actualHartreeSourceL1 hDensity hSob hH hab q),
      sourceL2ToL1_value (criticalPathIntervalSource hDensity hSob hH hab q 0)] with s hs hn
    change Lp.toTemperedDistribution ((E.sub (actualHartreeSourceL1 hDensity hSob hH hab q)).value s) _ = _
    rw [hs]
    change _ - Lp.toTemperedDistribution ((actualHartreeSourceL1 hDensity hSob hH hab q).value s) _ = _
    exact congrArg (fun v : SourceSpace =>
      Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) -
      Lp.toTemperedDistribution v (freeTest ((t : ℝ)-s) φ)) hn
  have hi := actual_hartree_future_pair_integrable hDensity hSob hH hab q E t φ
  exact (integral_congr_ae hAE).trans (integral_sub hi.2 hi.1)

variable {C0 Cr : ℝ} (h0 : OrdinaryEndpointBound C0)
  (hret : OrdinaryRetardedStrichartz h0 Cr)

include h0 hret

/-- Original compact Hartree PDE produces the literal right-endpoint Duhamel formula.
The signs are -i for the future Hartree integral and +i for the future error integral. -/
theorem actual_backward_literal_of_distributional
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hPDE : ForcedHartreeCompactTestIdentity alpha c hab q E)
    (t : Set.Icc a b) (φ : Test) :
    energyDistribution (energyPath _ q t) φ =
      FreeFlow.free ((t : ℝ)-b) (energyDistribution (energyPath _ q ⟨b, hab, le_rfl⟩)) φ -
        Complex.I * (∫ s in Set.Ioc (t : ℝ) b,
          Lp.toTemperedDistribution ((criticalPathIntervalSource hDensity hSob hH hab q 0).value s)
            (freeTest ((t : ℝ)-s) φ)) +
        Complex.I * ∫ s in Set.Ioc (t : ℝ) b,
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  let Q := extendEnergyPath hab (energyPath _ q)
  let F := totalHartreeSource hDensity hSob hH hab q E
  have he := (actual_domain_distributional_duhamel_at hDensity hSob h0 hret hab F
    hgen hUnique Q Q.continuous.continuousOn
    (totalHartreeSource_PDE hDensity hSob hH hab q E hPDE) ⟨b, hab, le_rfl⟩ t φ).2
  have hQt : Q t = energyPath _ q t := extendEnergyPath_val hab (energyPath _ q) t
  have hQb : Q b = energyPath _ q ⟨b, hab, le_rfl⟩ := by
    change energyPath _ q (Set.projIcc a b hab b) = _
    exact congrArg (fun s : Set.Icc a b => energyPath _ q s) (Set.projIcc_right hab)
  change energyDistribution (Q t) φ = FreeFlow.free ((t : ℝ)-b)
    (energyDistribution (Q b)) φ - Complex.I * ∫ s in b..(t : ℝ),
      Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) at he
  let k : ℝ → ℂ := fun s => Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ)
  let IE := ∫ s in Set.Ioc (t : ℝ) b,
    Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ)
  let IN := ∫ s in Set.Ioc (t : ℝ) b,
    Lp.toTemperedDistribution ((criticalPathIntervalSource hDensity hSob hH hab q 0).value s)
      (freeTest ((t : ℝ)-s) φ)
  have hi : (∫ s in Set.Ioc (t : ℝ) b, k s) = IE - IN :=
    totalHartreeSource_future_integral hDensity hSob hH hab q E t φ
  have hsign : (∫ s in b..(t : ℝ), k s) = -(IE - IN) :=
    (intervalIntegral.integral_symm (f := k) (μ := volume) (t : ℝ) b).trans
      (congrArg (fun z : ℂ => -z) ((intervalIntegral.integral_of_le (f := k) t.property.2).trans hi))
  have hright : FreeFlow.free ((t : ℝ)-b) (energyDistribution (Q b)) φ -
      Complex.I * (∫ s in b..(t : ℝ), k s) =
      FreeFlow.free ((t : ℝ)-b) (energyDistribution (energyPath _ q ⟨b, hab, le_rfl⟩)) φ -
      Complex.I * (-(IE-IN)) :=
    congrArg₂ (fun (g : EnergyState) (z : ℂ) =>
      FreeFlow.free ((t : ℝ)-b) (energyDistribution g) φ - Complex.I * z) hQb hsign
  exact (congrArg (fun g : EnergyState => energyDistribution g φ) hQt).symm.trans
    (he.trans (hright.trans (backward_scalar_algebra _ IE IN)))

end HartreeF.HartreeDistributionalBridge
