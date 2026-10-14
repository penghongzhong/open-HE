import FL1RetardedCriticalPathConsumer
import FActualFreeTestPairing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath.CompatibleL1IntervalSource
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain
open SobolevStretch StationarySelfTest Retarded ActualStrichartz FreeTestBounds
variable {a b : ℝ} (E : CompatibleL1IntervalSource a b)

/-- The original value is genuinely integrable in time. -/
theorem value_integrable : Integrable (E.value : ℝ → SourceSpace) (localMeasure a b) :=
  memLp_one_iff_integrable.mp (Lp.memLp E.value)

/-- The actual truncated L2 values are also integrable on the finite original interval. -/
theorem approximation_value_integrable (n : ℕ) :
    Integrable ((E.approximation n).value : ℝ → SourceSpace) (localMeasure a b) :=
  (Lp.memLp (E.approximation n).value).integrable (by norm_num)

/-- Restricting the original interval to its retarded past loses no L1 convergence. -/
theorem approximation_past_eLpNorm_tendsto_zero (t : ℝ) :
    Tendsto (fun n => eLpNorm (fun s => (E.approximation n).value s - E.value s)
      1 (volume.restrict (Set.Icc a b ∩ Set.Iio t))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    E.approximation_value_eLpNorm_tendsto_zero (fun _ => bot_le)
  intro n
  exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume Set.inter_subset_left)

/-- The untruncated scalar retarded integrand is an actual integrable function. -/
theorem retarded_scalar_integrable (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (t : ℝ) (φ : FreeFlow.Test) :
    IntegrableOn (fun s => Lp.toTemperedDistribution (E.value s) (freeTest (t-s) φ))
      (Set.Icc a b ∩ Set.Iio t) := by
  exact freeTestPair_integrable hDensity hSob
    (volume.restrict (Set.Icc a b ∩ Set.Iio t)) t φ E.value
    (E.value_integrable.mono_measure (Measure.restrict_mono_set volume Set.inter_subset_left))

/-- Actual L1 source convergence identifies the limit of the literal scalar integrals. -/
theorem approximation_scalar_integral_tendsto (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (t : ℝ) (φ : FreeFlow.Test) :
    Tendsto (fun n => ∫ s in Set.Icc a b ∩ Set.Iio t,
      Lp.toTemperedDistribution ((E.approximation n).value s) (freeTest (t-s) φ))
      atTop (𝓝 (∫ s in Set.Icc a b ∩ Set.Iio t,
        Lp.toTemperedDistribution (E.value s) (freeTest (t-s) φ))) :=
  freeTestPair_integral_tendsto_of_L1 hDensity hSob
    (volume.restrict (Set.Icc a b ∩ Set.Iio t)) t φ
    (fun n => (E.approximation n).value) E.value
    (fun n => (E.approximation_value_integrable n).mono_measure
      (Measure.restrict_mono_set volume Set.inter_subset_left))
    (E.value_integrable.mono_measure (Measure.restrict_mono_set volume Set.inter_subset_left))
    (E.approximation_past_eLpNorm_tendsto_zero t)

/-- The constructed Banach output is the literal retarded Duhamel distribution of the original L1 source. -/
theorem retardedCriticalPath_scalar (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t) φ =
      ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ),
        Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) :=
  tendsto_nhds_unique (L1RetardedConsumer.cutoff_scalar_integral_tendsto hDensity hSob h0 h E t φ)
    (E.approximation_scalar_integral_tendsto hDensity hSob t φ)

/-- The actual constructed distribution equals the usual forward Duhamel integral. -/
theorem retardedCriticalPath_forward_scalar (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t) φ =
      ∫ s in Set.Ioc a (t : ℝ),
        Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  rw [E.retardedCriticalPath_scalar hDensity hSob h0 h, intervalPast_eq_Ico,
    integral_Ico_eq_integral_Ioc]

/-- Existence, literal source identification, quantitative graph bound, and canonical convergence
are all outputs for the genuine L1-time source. -/
theorem exists_actual_retarded_path (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) :
    ∃ u : CriticalPath (intervalMeasure a b),
      (∀ t : Set.Icc a b, ∀ φ : FreeFlow.Test,
        energyDistribution (energyPath _ u t) φ =
          ∫ s in Set.Icc a b ∩ Set.Iio (t : ℝ),
            Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ)) ∧
      ‖u‖ ≤ max (energyEndpointConstant K C0) C * ‖E.gradient‖ ∧
      Tendsto (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n))
        atTop (𝓝 u) :=
  ⟨E.retardedCriticalPath hDensity hSob h0 h,
    E.retardedCriticalPath_scalar hDensity hSob h0 h,
    E.retardedCriticalPath_norm_le hDensity hSob h0 h,
    E.retarded_approximation_tendsto hDensity hSob h0 h⟩

end HartreeF.ActualDuhamelPath.CompatibleL1IntervalSource
