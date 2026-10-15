import FGaugeCompactParameterBounds
import FCriticalAffineL2Continuity

/-! Arbitrary affine normalizations between two nonzero compact carriers.
Intrinsic gauges are auxiliary witnesses, not hypotheses on the parameters. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open Filter Set
open scoped Topology
namespace HartreeF.Paper121AffineProperness
open EnergySpace CriticalAffine L6OrbitGauge

theorem compact_carriers_parameter_box {A B : Set EnergyState}
    (hA : IsCompact A) (hAzero : (0 : EnergyState) ∉ A)
    (hB : IsCompact B) (hBzero : (0 : EnergyState) ∉ B) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ f ∈ A, ∀ (r : ℝ) (hr : 0 < r) (y : Space),
        (criticalAffineState r hr y).symm f ∈ B →
          1 / C ≤ r ∧ r ≤ C ∧ ‖y‖ ≤ D := by
  obtain ⟨m, hm⟩ := gauge_parameters_bounded_on_compact hA hAzero
  obtain ⟨n, hn⟩ := gauge_parameters_bounded_on_compact hB hBzero
  let M : ℝ := (m : ℝ) + 1
  let N : ℝ := (n : ℝ) + 1
  let C : ℝ := 2 * M * N
  let D : ℝ := 3 * M + C * (3 * N)
  have hM : 0 < M := by dsimp [M]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C, D, hC, hD, ?_⟩
  intro f hf r hr y hv
  have hfzero : f ≠ 0 := fun h => hAzero (h ▸ hf)
  obtain ⟨R, x, hg⟩ := exists_gauge hfzero
  have hsource := hm f hf R x hg
  change 1 / M ≤ R ∧ R ≤ 2 * M ∧ ‖x‖ ≤ 3 * M at hsource
  let v := (criticalAffineState r hr y).symm f
  have hgv : Gauge v (R / r) (r⁻¹ • (x - y)) := by
    apply gauge_criticalAffine_pullback hr y
    simpa only [v, (criticalAffineState r hr y).apply_symm_apply] using hg
  have htarget := hn v hv (R / r) (r⁻¹ • (x - y)) hgv
  change 1 / N ≤ R / r ∧ R / r ≤ 2 * N ∧
    ‖r⁻¹ • (x - y)‖ ≤ 3 * N at htarget
  have hRr : R ≤ (2 * N) * r := (div_le_iff₀ hr).mp htarget.2.1
  have hone : 1 ≤ R * M := (div_le_iff₀ hM).mp hsource.1
  have hmul := mul_le_mul_of_nonneg_right hRr hM.le
  have hlower : 1 / C ≤ r := by
    apply (div_le_iff₀ hC).mpr
    dsimp only [C]
    nlinarith [hone, hmul]
  have hrR : (1 / N) * r ≤ R := (le_div_iff₀ hr).mp htarget.1
  have hrRN : r ≤ R * N := by
    calc
      r = r * (N⁻¹ * N) := by rw [inv_mul_cancel₀ hN.ne', mul_one]
      _ = ((1 / N) * r) * N := by ring
      _ ≤ R * N := mul_le_mul_of_nonneg_right hrR hN.le
  have hupper : r ≤ C :=
    hrRN.trans (mul_le_mul_of_nonneg_right hsource.2.1 hN.le)
  have hdist : ‖x - y‖ ≤ r * (3 * N) := by
    have h := htarget.2.2
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at h
    have h' := mul_le_mul_of_nonneg_left h hr.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] using h'
  have hy : ‖y‖ ≤ D := by
    calc
      ‖y‖ ≤ ‖x‖ + ‖y - x‖ := norm_le_norm_add_norm_sub x y
      _ = ‖x‖ + ‖x - y‖ := by rw [norm_sub_rev]
      _ ≤ 3 * M + r * (3 * N) := add_le_add hsource.2.2 hdist
      _ ≤ D := add_le_add_left
        (mul_le_mul_of_nonneg_right hupper (by positivity : 0 ≤ 3 * N)) _
  exact ⟨hlower, hupper, hy⟩

end HartreeF.Paper121AffineProperness
