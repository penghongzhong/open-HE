import FNonlocalBrezisLieb
import FStateEnergyCalculus
import PowerDensityDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace EnergyVariation StateEnergy ForcingDomain SharpOrdinary EnergyContinuity NonlocalBL
attribute [local irreducible] energySubmodule

/-- Quantitative interaction continuity on actual L6 balls. The center may vary. -/
theorem interactionLp_difference_bound_on_ball {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (u v : L6) (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) :
    |interactionLp alpha u-interactionLp alpha v| ≤
      (sharpHLSConstant alpha * ((3+alpha)*(B^(2+alpha)+B^(2+alpha))) *
        (B^(3+alpha)+B^(3+alpha))) * ‖u-v‖ := by
  have ha := hH.order_pos
  have ha3 := hH.order_lt_three
  have hc := (sharpHLSConstant_pos ha ha3).le
  have hp : 0 ≤ 3+alpha := by linarith
  have hdiff : (eLpNorm ((u : Space → ℂ)-(v : Space → ℂ)) 6 volume).toReal = ‖u-v‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub u v)]
  have hd := powerDensity_difference_bound ha ha3 (Lp.memLp u) (Lp.memLp v)
  rw [hdiff] at hd
  have hd' : (eLpNorm (powerDensity alpha u-powerDensity alpha v)
      (ENNReal.ofReal (densityExponent alpha)) volume).toReal ≤
      ((3+alpha)*(B^(2+alpha)+B^(2+alpha)))*‖u-v‖ := by
    refine hd.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    apply mul_le_mul_of_nonneg_left _ hp
    exact add_le_add (Real.rpow_le_rpow (norm_nonneg u) hu (by linarith))
      (Real.rpow_le_rpow (norm_nonneg v) hv (by linarith))
  have hs := add_le_add (powerDensity_real_norm_bound ha (Lp.memLp u) hu)
    (powerDensity_real_norm_bound ha (Lp.memLp v) hv)
  have hq := rieszQuadratic_difference_bound hH
    (powerDensity_memLp ha (Lp.memLp u)) (powerDensity_memLp ha (Lp.memLp v))
  change |DirectionalCoercivity.interaction alpha u-DirectionalCoercivity.interaction alpha v| ≤ _
  rw [interaction_eq_rieszQuadratic hOrd (Lp.memLp u), interaction_eq_rieszQuadratic hOrd (Lp.memLp v)]
  refine hq.trans ?_
  calc
    _ ≤ (sharpHLSConstant alpha * (((3+alpha)*(B^(2+alpha)+B^(2+alpha)))*‖u-v‖)) *
        (B^(3+alpha)+B^(3+alpha)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd' hc) hs
        (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        (mul_nonneg hc (mul_nonneg (mul_nonneg hp
          (add_nonneg (Real.rpow_nonneg (le_trans (norm_nonneg u) hu) _) (Real.rpow_nonneg (le_trans (norm_nonneg u) hu) _))) (norm_nonneg _)))
    _ = _ := by ring

/-- Small L6 differences give small Hartree interaction differences uniformly
for two bounded, otherwise moving, sequences. -/
theorem interactionLp_difference_tendsto_zero {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {u v : ℕ → L6} (hu : ∀ n, ‖u n‖ ≤ B) (hv : ∀ n, ‖v n‖ ≤ B)
    (hd : Tendsto (fun n => ‖u n-v n‖) atTop (𝓝 0)) :
    Tendsto (fun n => interactionLp alpha (u n)-interactionLp alpha (v n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := hd.const_mul
    (sharpHLSConstant alpha * ((3+alpha)*(B^(2+alpha)+B^(2+alpha))) * (B^(3+alpha)+B^(3+alpha)))
  simp only [mul_zero] at ht
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => interactionLp_difference_bound_on_ball hH hOrd (u n) (v n) (hu n) (hv n)) ht

private theorem norm_sq_difference_bound {E : Type*} [NormedAddCommGroup E]
    {a b : E} {B : ℝ} (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    |‖a‖^2-‖b‖^2| ≤ ‖a-b‖*(2*B) := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b)), mul_comm (‖a‖+‖b‖)]
  exact (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le a b)
    (add_nonneg (norm_nonneg a) (norm_nonneg b))).trans
    (mul_le_mul_of_nonneg_left (show ‖a‖+‖b‖ ≤ 2*B by linarith) (norm_nonneg _))

/-- Actual kinetic continuity on graph-norm bounded moving sequences. -/
theorem gradientSquared_difference_tendsto_zero {B : ℝ} {u v : ℕ → EnergyState}
    (hu : ∀ n, ‖u n‖ ≤ B) (hv : ∀ n, ‖v n‖ ≤ B)
    (hd : Tendsto (fun n => ‖u n-v n‖) atTop (𝓝 0)) :
    Tendsto (fun n => gradientSquared (u n)-gradientSquared (v n)) atTop (𝓝 0) := by
  have hB : 0 ≤ B := (norm_nonneg (u 0)).trans (hu 0)
  have ht (j : Fin 3) : Tendsto
      (fun n => ‖energyGradient j (u n)‖^2-‖energyGradient j (v n)‖^2) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hc := hd.mul_const (2*B)
    simp only [zero_mul] at hc
    apply squeeze_zero (fun n => norm_nonneg _) _ hc
    intro n
    refine (norm_sq_difference_bound ((energyState_gradient_norm_le (u n) j).trans (hu n))
      ((energyState_gradient_norm_le (v n) j).trans (hv n))).trans ?_
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hh := energyState_gradient_norm_le (u n-v n) j
    change ‖energyGradient j (u n-v n)‖ ≤ ‖u n-v n‖ at hh
    rwa [map_sub] at hh
  simpa only [gradientSquared, ← Finset.sum_sub_distrib, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ => ht j)

/-- Actual total-energy differences vanish on bounded moving sequences whose
full homogeneous graph difference tends to zero. No scalar L2 premise occurs. -/
theorem totalEnergy_difference_tendsto_zero {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {u v : ℕ → EnergyState} (hu : ∀ n, ‖u n‖ ≤ B) (hv : ∀ n, ‖v n‖ ≤ B)
    (hd : Tendsto (fun n => ‖u n-v n‖) atTop (𝓝 0)) :
    Tendsto (fun n => totalEnergy alpha (u n)-totalEnergy alpha (v n)) atTop (𝓝 0) := by
  have hval : Tendsto (fun n => ‖energyValue (u n)-energyValue (v n)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => by
      have hh := energyState_value_norm_le (u n-v n)
      change ‖energyValue (u n-v n)‖ ≤ ‖u n-v n‖ at hh
      rwa [map_sub] at hh) hd
  have hi := interactionLp_difference_tendsto_zero hH hOrd
    (u := fun n => energyValue (u n)) (v := fun n => energyValue (v n))
    (fun n => (energyState_value_norm_le (u n)).trans (hu n))
    (fun n => (energyState_value_norm_le (v n)).trans (hv n)) hval
  have hk := gradientSquared_difference_tendsto_zero hu hv hd
  have ht := (hk.div_const 2).sub (hi.div_const (2*(3+alpha)))
  simp only [zero_div, sub_zero] at ht
  convert ht using 1
  funext n
  simp only [totalEnergy]
  ring

#print axioms interactionLp_difference_bound_on_ball
#print axioms interactionLp_difference_tendsto_zero
#print axioms gradientSquared_difference_tendsto_zero
#print axioms totalEnergy_difference_tendsto_zero
end HartreeF.ProfileEnergy
