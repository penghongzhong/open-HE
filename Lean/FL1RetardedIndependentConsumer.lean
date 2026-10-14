import FL1RetardedScalarIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.L1RetardedIndependentReview
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain ActualDuhamelPath
open SobolevStretch StationarySelfTest Retarded ActualStrichartz
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace

/-- Every original compatible L2 source gives a genuine L1 source on any finite Icc. -/
def sourceL2ToL1 {a b : ℝ} (F : CompatibleIntervalSource a b) :
    CompatibleL1IntervalSource a b where
  value := (memLp_one_iff_integrable.mpr
    ((Lp.memLp F.value).integrable (by norm_num))).toLp F.value
  gradient := F.gradient
  derivative := by
    filter_upwards [F.derivative, (memLp_one_iff_integrable.mpr
      ((Lp.memLp F.value).integrable (by norm_num))).coeFn_toLp] with t hF hv
    intro j
    rw [hv]
    exact hF j

theorem sourceL2ToL1_value {a b : ℝ} (F : CompatibleIntervalSource a b) :
    ((sourceL2ToL1 F).value : ℝ → SourceSpace) =ᵐ[localMeasure a b] F.value :=
  (memLp_one_iff_integrable.mpr ((Lp.memLp F.value).integrable (by norm_num))).coeFn_toLp

/-- The extension agrees with the original actual L2 retarded map, with no a<b requirement. -/
theorem sourceL2ToL1_retarded_eq (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b) :
    (sourceL2ToL1 F).retardedCriticalPath hDensity hSob h0 h =
      intervalRetardedCriticalPath hDensity hSob h0 h F := by
  exact (sourceL2ToL1 F).retardedCriticalPath_eq_of_approximation hDensity hSob h0 h
    (fun _ => F) tendsto_const_nhds _ tendsto_const_nhds

/-- An actual zero source, including its actual spatial distributional derivative. -/
def zeroSource (a b : ℝ) : CompatibleL1IntervalSource a b where
  value := 0
  gradient := 0
  derivative := by
    filter_upwards [Lp.coeFn_zero SourceSpace 1 (localMeasure a b),
      Lp.coeFn_zero SourceSpace 2 (localMeasure a b)] with t hv hg
    intro j
    change ∂_{coordinate j} (Lp.toTemperedDistribution ((0 : Lp SourceSpace 1 (localMeasure a b)) t)) =
      Lp.toTemperedDistribution ((0 : LocalEndpointSource (Set.Icc a b)) t)
    rw [hv, hg]
    simp only [Pi.zero_apply]
    have hz : Lp.toTemperedDistribution (0 : SourceSpace) = (0 : FreeFlow.TD) :=
      map_zero (Lp.toTemperedDistributionCLM ℂ (volume : Measure FreeFlow.V)
        (ENNReal.ofReal (6/5 : ℝ)))
    rw [hz]
    exact map_zero (lineDerivOpCLM ℂ FreeFlow.TD (coordinate j))

theorem zero_gradient_output (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b)
    (hE : E.gradient = 0) : E.retardedCriticalPath hDensity hSob h0 h = 0 := by
  apply (norm_eq_zero (E := CriticalPath (intervalMeasure a b))).mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hE, norm_zero, mul_zero] using E.retardedCriticalPath_norm_le hDensity hSob h0 h

theorem zero_source_output (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) :
    (zeroSource a b).retardedCriticalPath hDensity hSob h0 h = 0 :=
  zero_gradient_output hDensity hSob h0 h (zeroSource a b) rfl

/-- The source in the integrability statement and both literal formulas is exactly E.value. -/
theorem scalar_realization (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b)
    (t : Set.Icc a b) (φ : FreeFlow.Test) :
    IntegrableOn (fun s => Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ))
      (Set.Icc a b ∩ Set.Iio (t : ℝ)) ∧
    energyDistribution (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t) φ =
      ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ),
        Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) ∧
    energyDistribution (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t) φ =
      ∫ s in Set.Ioc a (t : ℝ),
        Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) :=
  ⟨E.retarded_scalar_integrable hDensity hSob t φ,
    E.retardedCriticalPath_scalar hDensity hSob h0 h t φ,
    E.retardedCriticalPath_forward_scalar hDensity hSob h0 h t φ⟩

/-- Singleton intervals still return the proved zero initial energy state. -/
theorem singleton_energy_zero (hDensity : OrdinaryH1Density) {K C0 C a : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a a) :
    energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) ⟨a, le_rfl, le_rfl⟩ = 0 :=
  E.retardedCriticalPath_initial hDensity hSob h0 h le_rfl

theorem singleton_scalar_zero (hDensity : OrdinaryH1Density) {K C0 C a : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a a)
    (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h)
      ⟨a, le_rfl, le_rfl⟩) φ = 0 := by
  rw [E.retardedCriticalPath_forward_scalar hDensity hSob h0 h]
  simp only [Set.Ioc_self, setIntegral_empty]

/-- Two independently chosen compatible approximations approach one another in the actual graph norm. -/
theorem equivalent_approximations_difference_tendsto
    (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b)
    (F G : ℕ → CompatibleIntervalSource a b)
    (hF : Tendsto (fun n => (F n).gradient) atTop (𝓝 E.gradient))
    (hG : Tendsto (fun n => (G n).gradient) atTop (𝓝 E.gradient)) :
    Tendsto (fun n => ‖intervalRetardedCriticalPath hDensity hSob h0 h (F n) -
      intervalRetardedCriticalPath hDensity hSob h0 h (G n)‖) atTop (𝓝 0) := by
  have ht := L1RetardedConsumer.l1_extension_norm_tendsto (V := CriticalPath (intervalMeasure a b))
    (l1_extension_tendsto_sub (V := CriticalPath (intervalMeasure a b))
    (E.retarded_tendsto_of_gradient_tendsto hDensity hSob h0 h F hF)
    (E.retarded_tendsto_of_gradient_tendsto hDensity hSob h0 h G hG))
  simpa only [sub_self, norm_zero (E := CriticalPath (intervalMeasure a b))] using ht

/-- The output's actual energy gradient equals its spacetime coordinate almost everywhere. -/
theorem actual_graph_gradient_agreement (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b) (j : Fin 3) :
    ∀ᵐ t ∂intervalMeasure a b,
      (energyGradient j (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t) :
        FreeFlow.V → ℂ) =ᵐ[volume]
      (criticalGradient _ j (E.retardedCriticalPath hDensity hSob h0 h) t : FreeFlow.V → ℂ) :=
  criticalGradient_ae_eq _ (E.retardedCriticalPath hDensity hSob h0 h) j

end HartreeF.L1RetardedIndependentReview

set_option pp.universes true
#check @HartreeF.L1RetardedIndependentReview.sourceL2ToL1
#print axioms HartreeF.L1RetardedIndependentReview.sourceL2ToL1
#check @HartreeF.L1RetardedIndependentReview.sourceL2ToL1_value
#print axioms HartreeF.L1RetardedIndependentReview.sourceL2ToL1_value
#check @HartreeF.L1RetardedIndependentReview.sourceL2ToL1_retarded_eq
#print axioms HartreeF.L1RetardedIndependentReview.sourceL2ToL1_retarded_eq
#check @HartreeF.L1RetardedIndependentReview.zeroSource
#print axioms HartreeF.L1RetardedIndependentReview.zeroSource
#check @HartreeF.L1RetardedIndependentReview.zero_gradient_output
#print axioms HartreeF.L1RetardedIndependentReview.zero_gradient_output
#check @HartreeF.L1RetardedIndependentReview.zero_source_output
#print axioms HartreeF.L1RetardedIndependentReview.zero_source_output
#check @HartreeF.L1RetardedIndependentReview.scalar_realization
#print axioms HartreeF.L1RetardedIndependentReview.scalar_realization
#check @HartreeF.L1RetardedIndependentReview.singleton_energy_zero
#print axioms HartreeF.L1RetardedIndependentReview.singleton_energy_zero
#check @HartreeF.L1RetardedIndependentReview.singleton_scalar_zero
#print axioms HartreeF.L1RetardedIndependentReview.singleton_scalar_zero
#check @HartreeF.L1RetardedIndependentReview.equivalent_approximations_difference_tendsto
#print axioms HartreeF.L1RetardedIndependentReview.equivalent_approximations_difference_tendsto
#check @HartreeF.L1RetardedIndependentReview.actual_graph_gradient_agreement
#print axioms HartreeF.L1RetardedIndependentReview.actual_graph_gradient_agreement
