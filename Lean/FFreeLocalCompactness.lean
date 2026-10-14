import FFreeLowFrequencyLocal
import FFreeHighFrequencyLocal

/-! Original-sequence local compactness of the actual free Fourier orbit.
The high-frequency theorem is imported as a producer with a proof, never as an input.
Static uncompiled draft. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.FreeLocalCompactness
open MeasureTheory Filter
open scoped ENNReal Topology
open FreeFlow ActualStrichartz EnergySpace.Highpass

theorem lowL2_add_highL2 (q : Cutoff) (L : ℝ) (f : L2) :
    lowL2 q L f + highL2 q L f = f := by
  change lowL2 q L f + (f - lowL2 q L f) = f
  abel

theorem freeJoint_low_high_cylinder_ae (q : Cutoff) (L : ℝ)
    (f : L2) (T R : ℝ) (z : V) :
    Function.uncurry (freeJoint f) =ᵐ[cylinderMeasure T R z]
      fun p => freeJoint (lowL2 q L f) p.1 p.2 + freeJoint (highL2 q L f) p.1 p.2 := by
  simpa only [lowL2_add_highL2] using
    freeJoint_cylinder_add_ae (lowL2 q L f) (highL2 q L f) T R z

/-- Squared triangle inequality applied only after all three genuine domains exist. -/
theorem freeJoint_cylinder_split_integral_le (q : Cutoff) (L : ℝ)
    (f : L2) (T R : ℝ) (z : V) :
    (∫ p : ℝ × V, ‖freeJoint f p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z) ≤
      2 * (∫ p : ℝ × V, ‖freeJoint (lowL2 q L f) p.1 p.2‖ ^ 2
        ∂cylinderMeasure T R z) +
      2 * (∫ p : ℝ × V, ‖freeJoint (highL2 q L f) p.1 p.2‖ ^ 2
        ∂cylinderMeasure T R z) := by
  have hl := freeJoint_cylinder_integrable_sq (lowL2 q L f) T R z
  have hh := freeJoint_cylinder_integrable_sq (highL2 q L f) T R z
  have hb : (∫ p : ℝ × V, ‖freeJoint f p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z) ≤
      ∫ p : ℝ × V, (2 * ‖freeJoint (lowL2 q L f) p.1 p.2‖ ^ 2 +
        2 * ‖freeJoint (highL2 q L f) p.1 p.2‖ ^ 2) ∂cylinderMeasure T R z := by
    apply integral_mono_ae (freeJoint_cylinder_integrable_sq f T R z)
      ((hl.const_mul 2).add (hh.const_mul 2))
    filter_upwards [freeJoint_low_high_cylinder_ae q L f T R z] with p hp
    rw [hp]
    have ht := norm_add_le (freeJoint (lowL2 q L f) p.1 p.2)
      (freeJoint (highL2 q L f) p.1 p.2)
    have hab := norm_nonneg (freeJoint (lowL2 q L f) p.1 p.2 +
      freeJoint (highL2 q L f) p.1 p.2)
    have hs := pow_le_pow_left₀ hab ht 2
    nlinarith [sq_nonneg (‖freeJoint (lowL2 q L f) p.1 p.2‖ -
      ‖freeJoint (highL2 q L f) p.1 p.2‖)]
  simpa only [integral_add (hl.const_mul 2) (hh.const_mul 2), integral_const_mul] using hb

/-- First choose one frequency from epsilon and the explicit all-index cap.
Only after fixing that frequency is the original natural sequence sent to infinity. -/
theorem freeJoint_cylinder_integral_tendsto_zero (q : Cutoff) {f : ℕ → L2} {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ n, ‖f n‖ ≤ B)
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) (z : V) :
    Tendsto (fun n => ∫ p : ℝ × V, ‖freeJoint (f n) p.1 p.2‖ ^ 2
      ∂cylinderMeasure T R z) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le
      (integral_nonneg (fun p => sq_nonneg _)))
  · intro ε hε
    let C : ℝ := 24 * Real.sqrt 3 * R
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let L : ℝ := 1 + 4 * C * B ^ 2 / ε
    have hL : 0 < L := by dsimp [L]; positivity
    have htail : C / L * B ^ 2 < ε / 4 := by
      have hr : C / L * B ^ 2 = (C * B ^ 2) / L := by ring
      rw [hr]
      apply (div_lt_iff₀ hL).mpr
      have he : ε / 4 * L = ε / 4 + C * B ^ 2 := by
        dsimp [L]
        field_simp [hε.ne'] <;> ring
      rw [he]
      linarith
    have hlow := lowL2_cylinder_integral_tendsto_zero q hL hB hbound hweak T R z
    filter_upwards [hlow.eventually (gt_mem_nhds (by linarith : 0 < ε / 4))] with n hn
    have hh := highL2_local_bound q (f n) hT hR hL z
    have hbn : ‖f n‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbound n) 2
    have hhn : (∫ p : ℝ × V, ‖freeJoint (highL2 q L (f n)) p.1 p.2‖ ^ 2
        ∂cylinderMeasure T R z) < ε / 4 :=
      (hh.trans (mul_le_mul_of_nonneg_left hbn (div_nonneg hC hL.le))).trans_lt htail
    have hs := freeJoint_cylinder_split_integral_le q L (f n) T R z
    linarith

/-- Public scalar endpoint. This is the actual freeJoint representative and original sequence. -/
theorem freeJoint_local_tendsto_zero (q : Cutoff) {f : ℕ → L2} {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ n, ‖f n‖ ≤ B)
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) (z : V) :
    Tendsto (fun n => eLpNorm (Function.uncurry (freeJoint (f n))) 2
      (cylinderMeasure T R z)) atTop (𝓝 0) := by
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp
    ((Real.continuous_sqrt.tendsto 0).comp
      (freeJoint_cylinder_integral_tendsto_zero q hB hbound hweak hT hR z))
  have he (n : ℕ) := eLpNorm_two_eq_ofReal_sqrt (freeJoint_cylinder_memLp (f n) T R z)
  simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero, ← he] using h

theorem freeJoint_local_mixedNorm_tendsto_zero (q : Cutoff) {f : ℕ → L2} {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ n, ‖f n‖ ≤ B)
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) (z : V) :
    Tendsto (fun n => TimeHolder.mixedNorm (volume.restrict (Set.Icc (-T) T))
      (volume.restrict (Metric.ball z R)) 2 2 (freeJoint (f n))) atTop (𝓝 0) := by
  simpa only [freeJoint_cylinder_mixedNorm_eq] using
    freeJoint_local_tendsto_zero q hB hbound hweak hT hR z

end HartreeF.FreeLocalCompactness
