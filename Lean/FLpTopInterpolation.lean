import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {f : X → E}

/-- Global interpolation against L-infinity; the measure need not be finite. -/
theorem eLpNorm_interpolate_top {p q : ℝ} (hp : 0 < p) (hpq : p < q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      eLpNorm f ∞ μ ^ (1 - p / q) * eLpNorm f (ENNReal.ofReal p) μ ^ (p / q) := by
  have hq : 0 < q := lt_trans hp hpq
  have ht : 0 < p / q := div_pos hp hq
  have hb : 0 < 1 - p / q := sub_pos.mpr ((div_lt_one hq).mpr hpq)
  have hfac : (fun x => ‖f x‖) =
      (fun x => ‖f x‖ ^ (1 - p / q)) • (fun x => ‖f x‖ ^ (p / q)) := by
    funext x
    change ‖f x‖ = ‖f x‖ ^ (1 - p / q) * ‖f x‖ ^ (p / q)
    rw [← Real.rpow_add' (norm_nonneg _) (by linarith : 1 - p / q + p / q ≠ 0)]
    simp
  have hbmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ (1 - p / q)) μ :=
    (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hexp : ENNReal.ofReal q * ENNReal.ofReal (p / q) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul hq.le]
    congr 1
    field_simp
  calc
    _ = eLpNorm (fun x => ‖f x‖) (ENNReal.ofReal q) μ := (eLpNorm_norm f hf).symm
    _ = eLpNorm ((fun x => ‖f x‖ ^ (1 - p / q)) •
        (fun x => ‖f x‖ ^ (p / q))) (ENNReal.ofReal q) μ := by rw [hfac]
    _ ≤ eLpNorm (fun x => ‖f x‖ ^ (1 - p / q)) ∞ μ *
        eLpNorm (fun x => ‖f x‖ ^ (p / q)) (ENNReal.ofReal q) μ :=
      eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm _ hbmeas
    _ = _ := by
      rw [eLpNorm_norm_rpow f hf hb, eLpNorm_norm_rpow f hf ht,
        ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr hb)), hexp]

/-- The actual same measurable function gains every finite exponent above p. -/
theorem memLp_of_memLp_and_top {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hf : MemLp f (ENNReal.ofReal p) μ) (htop : MemLp f ∞ μ) :
    MemLp f (ENNReal.ofReal q) μ := by
  rcases hpq.eq_or_lt with h | h
  · simpa only [← h] using hf
  rw [memLp_iff]
  refine lt_of_le_of_lt
    (eLpNorm_interpolate_top hp h hf.aestronglyMeasurable) ?_
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by have := (div_lt_one (lt_trans hp h)).mpr h; linarith)
      htop.eLpNorm_ne_top
  · exact ENNReal.rpow_lt_top_of_nonneg (div_pos hp (lt_trans hp h)).le hf.eLpNorm_ne_top

end HartreeF.BoundedHartreeGradient
