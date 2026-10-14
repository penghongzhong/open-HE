import FL1RetardedCriticalPath

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.L1RetardedConsumer
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain ActualDuhamelPath
open SobolevStretch StationarySelfTest Retarded ActualStrichartz
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace

theorem l1_extension_norm_tendsto {V : Type*} [SeminormedAddCommGroup V]
    {f : ℕ → V} {x : V} (hf : Tendsto f atTop (𝓝 x)) :
    Tendsto (fun n => ‖f n‖) atTop (𝓝 ‖x‖) := hf.norm

/-- An actual output exists from the genuine L1 value and actual L2 derivatives alone. -/
theorem exists_retarded_path (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b) :
    ∃ u : CriticalPath (intervalMeasure a b),
      Tendsto (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n))
        atTop (𝓝 u) ∧
      ‖u‖ ≤ max (energyEndpointConstant K C0) C * ‖E.gradient‖ :=
  ⟨E.retardedCriticalPath hDensity hSob h0 h,
    E.retarded_approximation_tendsto hDensity hSob h0 h,
    E.retardedCriticalPath_norm_le hDensity hSob h0 h⟩

/-- The canonical cutoff has an explicit gradient-error convergence rate. -/
theorem canonical_approximation_error (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b) (n : ℕ) :
    ‖intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n) -
      E.retardedCriticalPath hDensity hSob h0 h‖ ≤
      max (energyEndpointConstant K C0) C * ‖(E.approximation n).gradient - E.gradient‖ :=
  E.intervalRetarded_sub_retardedCriticalPath_norm_le hDensity hSob h0 h (E.approximation n)

/-- The actual truncated scalar integrals converge to the constructed distribution's test value. -/
theorem cutoff_scalar_integral_tendsto (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b)
    (t : Set.Icc a b) (φ : FreeFlow.Test) :
    Tendsto (fun n => ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ),
      Lp.toTemperedDistribution ((E.approximation n).value s) (freeTest ((t : ℝ) - s) φ))
      atTop (𝓝 (energyDistribution (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t) φ)) := by
  simpa only [intervalRetardedCriticalPath_scalar] using
    E.retarded_approximation_scalar_tendsto hDensity hSob h0 h t φ

/-- The extension's energy coordinate retains the sharper original endpoint constant. -/
theorem actual_energy_norm_le (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b) :
    ‖energyPath _ (E.retardedCriticalPath hDensity hSob h0 h)‖ ≤
      energyEndpointConstant K C0 * ‖E.gradient‖ := by
  have ht := (energyPath (intervalMeasure a b)).continuous.tendsto
    (E.retardedCriticalPath hDensity hSob h0 h) |>.comp
      (E.retarded_approximation_tendsto hDensity hSob h0 h)
  apply le_of_tendsto' (l1_extension_norm_tendsto (V := C(Set.Icc a b, EnergyState)) ht)
  intro n
  exact (intervalRetardedCriticalPath_energy_norm hDensity hSob h0 h (E.approximation n)).trans
    (mul_le_mul_of_nonneg_left (E.approximation_gradient_norm_le n)
      (energyEndpointConstant_nonneg h0))

/-- Each actual critical gradient coordinate retains its numerical retarded constant. -/
theorem actual_gradient_norm_le (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b) (j : Fin 3) :
    ‖criticalGradient _ j (E.retardedCriticalPath hDensity hSob h0 h)‖ ≤ C * ‖E.gradient j‖ := by
  have ht := (criticalGradient (intervalMeasure a b) j).continuous.tendsto
    (E.retardedCriticalPath hDensity hSob h0 h) |>.comp
      (E.retarded_approximation_tendsto hDensity hSob h0 h)
  apply le_of_tendsto' (l1_extension_norm_tendsto ht)
  intro n
  have hb := intervalRetardedCriticalPath_gradient_bound hDensity hSob h0 h (E.approximation n) j
  have hr : ‖criticalGradient _ j (intervalRetardedCriticalPath hDensity hSob h0 h
      (E.approximation n))‖ ≤ C * ‖(E.approximation n).gradient j‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg h.1 (norm_nonneg _))).mp
    simpa only [ofReal_norm] using hb
  exact hr.trans (mul_le_mul_of_nonneg_left (E.approximation_gradient_component_norm_le n j) h.1)

/-- Two valid gradient-convergent approximations have the same actual path limit. -/
theorem approximation_limits_equal (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (E : CompatibleL1IntervalSource a b)
    (F G : ℕ → CompatibleIntervalSource a b)
    (hF : Tendsto (fun n => (F n).gradient) atTop (𝓝 E.gradient))
    (hG : Tendsto (fun n => (G n).gradient) atTop (𝓝 E.gradient))
    (u v : CriticalPath (intervalMeasure a b))
    (hu : Tendsto (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (F n)) atTop (𝓝 u))
    (hv : Tendsto (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (G n)) atTop (𝓝 v)) :
    u = v :=
  (E.retardedCriticalPath_eq_of_approximation hDensity hSob h0 h F hF u hu).symm.trans
    (E.retardedCriticalPath_eq_of_approximation hDensity hSob h0 h G hG v hv)

end HartreeF.L1RetardedConsumer
