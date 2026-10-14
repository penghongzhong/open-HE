import FCompatibleIntervalSource
import FiniteLpTail

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open IntervalTimeTransport EnergySpace Retarded

/-- A time-L1 source with its actual time-L2 spatial weak derivatives. -/
structure CompatibleL1IntervalSource (a b : ℝ) where
  value : Lp SourceSpace 1 (localMeasure a b)
  gradient : Fin 3 → LocalEndpointSource (Set.Icc a b)
  derivative : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
    ∂_{coordinate j} (Lp.toTemperedDistribution (value t)) =
      Lp.toTemperedDistribution (gradient j t)

namespace CompatibleL1IntervalSource
variable {a b : ℝ} (E : CompatibleL1IntervalSource a b)

/-- The cutoff depends only on time, through the norm of the spatial source. -/
def timeCutoffSet (n : ℕ) : Set ℝ := {t | ‖E.value t‖ ≤ (n : ℝ)}

theorem measurableSet_timeCutoffSet (n : ℕ) : MeasurableSet (E.timeCutoffSet n) :=
  measurableSet_le (Lp.stronglyMeasurable E.value).norm.measurable measurable_const

theorem timeCutoffSet_eventually_mem (t : ℝ) :
    ∀ᶠ n in atTop, t ∈ E.timeCutoffSet n := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖E.value t‖
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN.le.trans (Nat.cast_le.mpr hn)

theorem approximation_value_memLp (n : ℕ) :
    MemLp ((E.timeCutoffSet n).indicator E.value) 2 (localMeasure a b) := by
  apply MemLp.of_bound
    ((Lp.aestronglyMeasurable E.value).indicator (E.measurableSet_timeCutoffSet n)) (n : ℝ)
  filter_upwards [] with t
  by_cases ht : t ∈ E.timeCutoffSet n
  · simpa only [Set.indicator_of_mem ht] using (show ‖E.value t‖ ≤ (n : ℝ) from ht)
  · simp only [Set.indicator_of_notMem ht, norm_zero]
    exact Nat.cast_nonneg n

/-- A common time indicator preserves the actual spatial derivative equation. -/
def approximation (n : ℕ) : CompatibleIntervalSource a b where
  value := (E.approximation_value_memLp n).toLp ((E.timeCutoffSet n).indicator E.value)
  gradient := fun j => ((Lp.memLp (E.gradient j)).indicator
    (E.measurableSet_timeCutoffSet n).nullMeasurableSet).toLp ((E.timeCutoffSet n).indicator (E.gradient j))
  derivative := by
    have hgrad := ae_all_iff.mpr (fun j =>
      ((Lp.memLp (E.gradient j)).indicator (E.measurableSet_timeCutoffSet n).nullMeasurableSet).coeFn_toLp)
    filter_upwards [E.derivative, (E.approximation_value_memLp n).coeFn_toLp, hgrad]
      with t hE hv hg
    intro j
    rw [hv, hg j]
    by_cases ht : t ∈ E.timeCutoffSet n
    · simpa only [Set.indicator_of_mem ht] using hE j
    · simp only [Set.indicator_of_notMem ht]
      have hz : Lp.toTemperedDistribution (0 : SourceSpace) = (0 : FreeFlow.TD) :=
        map_zero (Lp.toTemperedDistributionCLM ℂ (volume : Measure FreeFlow.V)
          (ENNReal.ofReal (6/5 : ℝ)))
      rw [hz]
      exact map_zero (lineDerivOpCLM ℂ FreeFlow.TD (coordinate j))

theorem approximation_value_coeFn (n : ℕ) :
    ((E.approximation n).value : ℝ → SourceSpace) =ᵐ[localMeasure a b]
      (E.timeCutoffSet n).indicator E.value :=
  (E.approximation_value_memLp n).coeFn_toLp

theorem approximation_gradient_coeFn (n : ℕ) (j : Fin 3) :
    ((E.approximation n).gradient j : ℝ → SourceSpace) =ᵐ[localMeasure a b]
      (E.timeCutoffSet n).indicator (E.gradient j) :=
  ((Lp.memLp (E.gradient j)).indicator (E.measurableSet_timeCutoffSet n).nullMeasurableSet).coeFn_toLp

theorem approximation_derivative (n : ℕ) :
    ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
      ∂_{coordinate j} (Lp.toTemperedDistribution ((E.approximation n).value t)) =
        Lp.toTemperedDistribution ((E.timeCutoffSet n).indicator (E.gradient j) t) := by
  have hg := ae_all_iff.mpr (E.approximation_gradient_coeFn n)
  filter_upwards [(E.approximation n).derivative, hg] with t ht hgt
  intro j
  rw [← hgt j]
  exact ht j

theorem approximation_gradient_component_norm_le (n : ℕ) (j : Fin 3) :
    ‖(E.approximation n).gradient j‖ ≤ ‖E.gradient j‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [E.approximation_gradient_coeFn n j] with t ht
  rw [ht]
  exact norm_indicator_le_norm_self _ _

theorem approximation_gradient_norm_le (n : ℕ) :
    ‖(E.approximation n).gradient‖ ≤ ‖E.gradient‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  exact (E.approximation_gradient_component_norm_le n j).trans (norm_le_pi_norm _ j)

theorem approximation_value_eLpNorm_tendsto_zero :
    Tendsto (fun n => eLpNorm (fun t => (E.approximation n).value t - E.value t)
      1 (localMeasure a b)) atTop (𝓝 0) := by
  have ht := CutoffApproximation.tendsto_eLpNorm_indicator_eventually_empty
    (Lp.memLp E.value) (by norm_num : (1 : ℝ≥0∞) ≠ 0) (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    (fun n => (E.measurableSet_timeCutoffSet n).compl)
    (ae_of_all _ (fun t => by simpa only [Set.notMem_compl_iff] using E.timeCutoffSet_eventually_mem t))
  apply ht.congr
  intro n
  rw [← eLpNorm_neg]
  apply eLpNorm_congr_ae
  filter_upwards [E.approximation_value_coeFn n] with t ht
  rw [ht]
  by_cases hm : t ∈ E.timeCutoffSet n
  · simp [hm]
  · simp [hm]

theorem approximation_gradient_component_norm_tendsto_zero (j : Fin 3) :
    Tendsto (fun n => ‖(E.approximation n).gradient j - E.gradient j‖) atTop (𝓝 0) := by
  have ht := CutoffApproximation.tendsto_eLpNorm_indicator_eventually_empty
    (Lp.memLp (E.gradient j)) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    (fun n => (E.measurableSet_timeCutoffSet n).compl)
    (ae_of_all _ (fun t => by simpa only [Set.notMem_compl_iff] using E.timeCutoffSet_eventually_mem t))
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  simp only [ENNReal.toReal_zero] at hreal
  apply hreal.congr
  intro n
  rw [Lp.norm_def]
  apply congrArg ENNReal.toReal
  rw [← eLpNorm_neg]
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub ((E.approximation n).gradient j) (E.gradient j),
    E.approximation_gradient_coeFn n j] with t hs ht
  simp only [Pi.neg_apply]
  rw [hs, Pi.sub_apply, ht]
  by_cases hm : t ∈ E.timeCutoffSet n
  · simp [hm]
  · simp [hm]

theorem approximation_gradient_tendsto :
    Tendsto (fun n => (E.approximation n).gradient) atTop (𝓝 E.gradient) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (E.approximation_gradient_component_norm_tendsto_zero j)

theorem approximation_gradient_norm_tendsto_zero :
    Tendsto (fun n => ‖(E.approximation n).gradient - E.gradient‖) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp E.approximation_gradient_tendsto

end CompatibleL1IntervalSource
end HartreeF.ActualDuhamelPath
