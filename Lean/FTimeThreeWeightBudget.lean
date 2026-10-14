import FTimeFiniteNormBridge
import FTimeSpatialWeights

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory GradientMajorants
open scoped ENNReal NNReal

def threeWeightBudget {T : Type*} [MeasurableSpace T] (alpha : ℝ)
    (mu : Measure T) (V W Y Z : T → Space → ℝ) : ℝ≥0∞ :=
  eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ^ (2 * alpha) *
      eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ^ (4 : ℝ) *
      eLpNorm (fun t => spatialNorm (30/13) (Z t)) 10 mu +
  eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ^ (2 * alpha) *
      eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ^ (3 : ℝ) *
      eLpNorm (fun t => spatialNorm (30/13) (Y t)) 10 mu *
      eLpNorm (fun t => spatialNorm 10 (W t)) 10 mu +
  eLpNorm (fun t => spatialNorm 6 (V t)) ∞ mu ^ (5 * alpha / 3) *
      eLpNorm (fun t => spatialNorm 10 (V t)) 10 mu ^ (4 - theta alpha) *
      eLpNorm (fun t => spatialNorm (30/13) (Y t)) 10 mu *
      eLpNorm (fun t => spatialNorm 6 (W t)) ∞ mu ^ (alpha / 3) *
      eLpNorm (fun t => spatialNorm 10 (W t)) 10 mu ^ theta alpha

theorem three_weight_time_bound {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (V W Y Z : T → Space → ℝ)
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hW : AEStronglyMeasurable (fun z : T × Space => W z.1 z.2) (mu.prod volume))
    (hY : AEStronglyMeasurable (fun z : T × Space => Y z.1 z.2) (mu.prod volume))
    (hZ : AEStronglyMeasurable (fun z : T × Space => Z z.1 z.2) (mu.prod volume)) :
    eLpNorm (fun t => singleWeight alpha (V t) (Z t) +
      spacetimeDifferenceWeight alpha (V t) (W t) (Y t) +
      mixedDifferenceWeight alpha (V t) (W t) (Y t)) 2 mu ≤
      threeWeightBudget alpha mu V W Y Z := by
  have h1 := single_weight_time_bound ha mu V Z hV hZ
  have h2 := spacetime_difference_weight_time_bound ha mu V W Y hV hW hY
  have h3 := mixed_difference_weight_time_bound ha ha3 mu V W Y hV hW hY
  calc
    _ = eLpNorm ((fun t => singleWeight alpha (V t) (Z t)) +
        (fun t => spacetimeDifferenceWeight alpha (V t) (W t) (Y t)) +
        (fun t => mixedDifferenceWeight alpha (V t) (W t) (Y t))) 2 mu := rfl
    _ ≤ (eLpNorm (fun t => singleWeight alpha (V t) (Z t)) 2 mu +
        eLpNorm (fun t => spacetimeDifferenceWeight alpha (V t) (W t) (Y t)) 2 mu) +
        eLpNorm (fun t => mixedDifferenceWeight alpha (V t) (W t) (Y t)) 2 mu :=
      (eLpNorm_add_le (by norm_num)).trans
        (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3

theorem finite_dominated_three_weights {alpha : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
    (C : ℝ≥0) (a : T → ℝ≥0∞) (V W Y Z : T → Space → ℝ)
    (haMeas : AEStronglyMeasurable a mu) (haFin : ∀ᵐ t ∂mu, a t ≠ ∞)
    (hV : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (mu.prod volume))
    (hW : AEStronglyMeasurable (fun z : T × Space => W z.1 z.2) (mu.prod volume))
    (hY : AEStronglyMeasurable (fun z : T × Space => Y z.1 z.2) (mu.prod volume))
    (hZ : AEStronglyMeasurable (fun z : T × Space => Z z.1 z.2) (mu.prod volume))
    (hb : ∀ᵐ t ∂mu, (a t).toReal ≤ (C : ℝ) *
      (singleWeight alpha (V t) (Z t) + spacetimeDifferenceWeight alpha (V t) (W t) (Y t) +
        mixedDifferenceWeight alpha (V t) (W t) (Y t))) :
    eLpNorm a 2 mu ≤ (C : ℝ≥0∞) * threeWeightBudget alpha mu V W Y Z := by
  rw [finite_extended_norm_bridge mu 2 a haMeas haFin]
  let g : T → ℝ := fun t => singleWeight alpha (V t) (Z t) +
    spacetimeDifferenceWeight alpha (V t) (W t) (Y t) + mixedDifferenceWeight alpha (V t) (W t) (Y t)
  have hmono : eLpNorm (fun t => (a t).toReal) 2 mu ≤ eLpNorm ((C : ℝ) • g) 2 mu := by
    apply eLpNorm_mono_ae haMeas.aemeasurable.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hb] with t hbt
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact hbt.trans (le_abs_self _)
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal C.coe_nonneg, ENNReal.ofReal_coe_nnreal] at hmono
  exact hmono.trans (mul_le_mul' le_rfl (three_weight_time_bound ha ha3 mu V W Y Z hV hW hY hZ))

end HartreeF.TimeHolder
