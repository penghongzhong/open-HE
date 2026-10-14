import RieszPairIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
Actual nonnegative compact density truncations and convergence of physical
pair integrals. This is a producer for the homogeneous extension step of
the written directional proof, not a Riesz/Fourier theorem or a proof of
convexity of the integrable-density energy. No Sobolev convergence of roots
of the truncated density is asserted or required.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.PhysicalDensity

/-- Simultaneous spatial and amplitude cutoff, defined for actual real densities. -/
def truncate (b : Space → ℝ) (n : ℕ) : Space → ℝ :=
  (Metric.closedBall 0 (n : ℝ)).indicator (fun x => min (b x) (n : ℝ))

theorem truncate_nonneg {b : Space → ℝ} (hb : ∀ x, 0 ≤ b x) (n : ℕ) (x : Space) :
    0 ≤ truncate b n x := by
  unfold truncate
  by_cases hx : x ∈ Metric.closedBall (0 : Space) (n : ℝ)
  · simp only [Set.indicator_of_mem hx]
    exact le_min (hb x) (Nat.cast_nonneg n)
  · simp [Set.indicator_of_notMem hx]

theorem truncate_le {b : Space → ℝ} (hb : ∀ x, 0 ≤ b x) (n : ℕ) (x : Space) :
    truncate b n x ≤ b x := by
  unfold truncate
  by_cases hx : x ∈ Metric.closedBall (0 : Space) (n : ℝ)
  · simpa only [Set.indicator_of_mem hx] using min_le_left (b x) (n : ℝ)
  · simpa only [Set.indicator_of_notMem hx] using hb x

theorem truncate_le_cutoff {b : Space → ℝ} (n : ℕ) (x : Space) :
    truncate b n x ≤ (n : ℝ) := by
  unfold truncate
  by_cases hx : x ∈ Metric.closedBall (0 : Space) (n : ℝ)
  · simpa only [Set.indicator_of_mem hx] using min_le_right (b x) (n : ℝ)
  · simpa only [Set.indicator_of_notMem hx] using Nat.cast_nonneg n

theorem truncate_aestronglyMeasurable {b : Space → ℝ}
    (hb : AEStronglyMeasurable b volume) (n : ℕ) :
    AEStronglyMeasurable (truncate b n) volume := by
  exact ((hb.aemeasurable.min aemeasurable_const).aestronglyMeasurable).indicator
    measurableSet_closedBall

theorem truncate_integrable {b : Space → ℝ}
    (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x) (n : ℕ) :
    Integrable (truncate b n) volume := by
  have hdom : Integrable
      ((Metric.closedBall (0 : Space) (n : ℝ)).indicator (fun _ => (n : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (C := (n : ℝ)) measure_closedBall_lt_top.ne)
  apply hdom.mono' (truncate_aestronglyMeasurable hb n)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (truncate_nonneg hb0 n x)]
  unfold truncate
  by_cases hx : x ∈ Metric.closedBall (0 : Space) (n : ℝ)
  · simp only [Set.indicator_of_mem hx]
    exact min_le_right _ _
  · simp [Set.indicator_of_notMem hx]

theorem truncate_eventually_eq (b : Space → ℝ) (x : Space) :
    ∀ᶠ n : ℕ in atTop, truncate b n x = b x := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max ‖x‖ (b x))
  refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hx : x ∈ Metric.closedBall (0 : Space) (n : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (le_max_left ‖x‖ (b x)).trans (hN.trans hnR)
  have hb : b x ≤ (n : ℝ) := (le_max_right ‖x‖ (b x)).trans (hN.trans hnR)
  simp only [truncate, Set.indicator_of_mem hx, min_eq_left hb]

theorem truncate_tendsto (b : Space → ℝ) (x : Space) :
    Tendsto (fun n : ℕ => truncate b n x) atTop (𝓝 (b x)) :=
by
  apply tendsto_const_nhds.congr'
  filter_upwards [truncate_eventually_eq b x] with n hn
  exact hn.symm

theorem truncate_eq_zero_of_outside (b : Space → ℝ) (n : ℕ) {x : Space}
    (hx : (n : ℝ) < ‖x‖) : truncate b n x = 0 := by
  have hout : x ∉ Metric.closedBall (0 : Space) (n : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  exact Set.indicator_of_notMem hout _

theorem truncate_monotone {b : Space → ℝ} (hb : ∀ x, 0 ≤ b x) (x : Space) :
    Monotone (fun n : ℕ => truncate b n x) := by
  intro m n hmn
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  by_cases hm : x ∈ Metric.closedBall (0 : Space) (m : ℝ)
  · have hn : x ∈ Metric.closedBall (0 : Space) (n : ℝ) :=
      Metric.closedBall_subset_closedBall hmnR hm
    simp only [truncate, Set.indicator_of_mem hm, Set.indicator_of_mem hn]
    exact min_le_min_left _ hmnR
  · simpa only [truncate, Set.indicator_of_notMem hm] using truncate_nonneg hb n x

/-- Pair densities use the same second-then-first order as rieszPairDensity. -/
def pairDensity (K : Space × Space → ℝ) (b : Space → ℝ) (z : Space × Space) : ℝ :=
  K z * b z.2 * b z.1

theorem pairDensity_nonneg {K : Space × Space → ℝ} {b : Space → ℝ}
    (hK : ∀ z, 0 ≤ K z) (hb : ∀ x, 0 ≤ b x) (z : Space × Space) :
    0 ≤ pairDensity K b z := mul_nonneg (mul_nonneg (hK z) (hb z.2)) (hb z.1)

theorem truncated_pair_le {K : Space × Space → ℝ} {b : Space → ℝ}
    (hK : ∀ z, 0 ≤ K z) (hb : ∀ x, 0 ≤ b x) (n : ℕ) (z : Space × Space) :
    pairDensity K (truncate b n) z ≤ pairDensity K b z := by
  unfold pairDensity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (truncate_le hb n z.2) (hK z))
    (truncate_le hb n z.1) (truncate_nonneg hb n z.1)
    (mul_nonneg (hK z) (hb z.2))

theorem pairDensity_aestronglyMeasurable {K : Space × Space → ℝ} {b : Space → ℝ}
    (hK : AEStronglyMeasurable K (volume.prod volume))
    (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (pairDensity K b) (volume.prod volume) :=
  (hK.mul hb.comp_snd).mul hb.comp_fst

theorem truncated_pair_integrable {K : Space × Space → ℝ} {b : Space → ℝ}
    (hK : AEStronglyMeasurable K (volume.prod volume))
    (hK0 : ∀ z, 0 ≤ K z) (hb : AEStronglyMeasurable b volume)
    (hb0 : ∀ x, 0 ≤ b x) (hint : Integrable (pairDensity K b) (volume.prod volume))
    (n : ℕ) : Integrable (pairDensity K (truncate b n)) (volume.prod volume) := by
  apply hint.mono' (pairDensity_aestronglyMeasurable hK (truncate_aestronglyMeasurable hb n))
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (pairDensity_nonneg hK0 (truncate_nonneg hb0 n) z)]
  exact truncated_pair_le hK0 hb0 n z

theorem truncated_pair_integral_tendsto {K : Space × Space → ℝ} {b : Space → ℝ}
    (hK : AEStronglyMeasurable K (volume.prod volume))
    (hK0 : ∀ z, 0 ≤ K z) (hb : AEStronglyMeasurable b volume)
    (hb0 : ∀ x, 0 ≤ b x) (hint : Integrable (pairDensity K b) (volume.prod volume)) :
    Tendsto (fun n : ℕ => ∫ z, pairDensity K (truncate b n) z ∂volume.prod volume)
      atTop (𝓝 (∫ z, pairDensity K b z ∂volume.prod volume)) := by
  apply tendsto_integral_of_dominated_convergence (pairDensity K b)
    (fun n => pairDensity_aestronglyMeasurable hK (truncate_aestronglyMeasurable hb n)) hint
  · intro n
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pairDensity_nonneg hK0 (truncate_nonneg hb0 n) z)]
    exact truncated_pair_le hK0 hb0 n z
  · filter_upwards [] with z
    exact (tendsto_const_nhds.mul (truncate_tendsto b z.2)).mul (truncate_tendsto b z.1)

theorem truncated_pair_integral_le {K : Space × Space → ℝ} {b : Space → ℝ}
    (hK : AEStronglyMeasurable K (volume.prod volume))
    (hK0 : ∀ z, 0 ≤ K z) (hb : AEStronglyMeasurable b volume)
    (hb0 : ∀ x, 0 ≤ b x) (hint : Integrable (pairDensity K b) (volume.prod volume))
    (n : ℕ) :
    (∫ z, pairDensity K (truncate b n) z ∂volume.prod volume) ≤
      ∫ z, pairDensity K b z ∂volume.prod volume := by
  exact integral_mono (truncated_pair_integrable hK hK0 hb hb0 hint n) hint
    (truncated_pair_le hK0 hb0 n)

theorem hartree_truncated_density_integrable (α : ℝ) {f : Space → ℂ}
    (hf : MemLp f 6 volume) (n : ℕ) :
    Integrable (truncate (powerDensity α f) n) volume := by
  apply truncate_integrable
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  · intro x
    unfold powerDensity
    positivity

/-- Literal Riesz energy truncation for actual L6 Hartree data. -/
theorem hartree_density_truncation_tendsto {α c : ℝ}
    (hHLS : ForcingDomain.OrdinaryHLS α c) {f : Space → ℂ} (hf : MemLp f 6 volume) :
    Tendsto (fun n : ℕ => ∫ z : Space × Space,
      rieszKernel α c (z.1-z.2) * truncate (powerDensity α f) n z.2 *
        truncate (powerDensity α f) n z.1 ∂volume.prod volume)
      atTop (𝓝 (∫ x, potential α c f x * powerDensity α f x)) := by
  rw [← PressureDomain.hartree_energy_pair_identity hHLS hf]
  apply truncated_pair_integral_tendsto
  · exact (measurable_const.mul
      (((continuous_fst.sub continuous_snd).norm.measurable).pow_const (α-3))).aestronglyMeasurable
  · intro z
    exact mul_nonneg hHLS.normalization_pos.le (Real.rpow_nonneg (norm_nonneg _) _)
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  · intro x
    unfold powerDensity
    positivity
  · exact PressureDomain.rieszPairDensity_integrable hHLS hf

#print axioms truncate_nonneg
#print axioms truncate_le
#print axioms truncate_le_cutoff
#print axioms truncate_aestronglyMeasurable
#print axioms truncate_integrable
#print axioms truncate_eventually_eq
#print axioms truncate_tendsto
#print axioms truncate_eq_zero_of_outside
#print axioms truncate_monotone
#print axioms pairDensity_nonneg
#print axioms truncated_pair_le
#print axioms pairDensity_aestronglyMeasurable
#print axioms truncated_pair_integrable
#print axioms truncated_pair_integral_tendsto
#print axioms truncated_pair_integral_le
#print axioms hartree_truncated_density_integrable
#print axioms hartree_density_truncation_tendsto
end HartreeF.PhysicalDensity
