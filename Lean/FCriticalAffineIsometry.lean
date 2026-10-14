import FCriticalAffineEnergy
import FStateSharpGroundThreshold

/-! Complex linear isometric equivalence on the existing EnergyState norm,
with the paper's positive length-scale/translation convention. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.CriticalAffine
open EnergySpace StateEnergy EnergyVariation ForcingDomain StateSharpThreshold
attribute [local irreducible] energySubmodule

theorem affineState_add {a : ℝ} (ha : 0 < a) (b : Space) (u v : EnergyState) :
    affineState ha b (u+v) = affineState ha b u + affineState ha b v := by
  apply energyValue_injective
  rw [map_add]
  apply Lp.ext
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae
    (Lp.coeFn_add (energyValue u) (energyValue v))
  filter_upwards [affineState_value_ae ha b (u+v), affineState_value_ae ha b u,
    affineState_value_ae ha b v,
    Lp.coeFn_add (energyValue (affineState ha b u)) (energyValue (affineState ha b v)), hi]
    with x hs hu hv ho hi
  simp only [valuePullback, map_add] at hs hu hv
  simp only [Pi.add_apply] at hi ho
  rw [hs, hi, smul_add, ho, hu, hv]

theorem affineState_smul {a : ℝ} (ha : 0 < a) (b : Space) (c : ℂ) (u : EnergyState) :
    affineState ha b (c • u) = c • affineState ha b u := by
  apply energyValue_injective
  rw [map_smul]
  apply Lp.ext
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae (Lp.coeFn_smul c (energyValue u))
  filter_upwards [affineState_value_ae ha b (c • u), affineState_value_ae ha b u,
    Lp.coeFn_smul c (energyValue (affineState ha b u)), hi] with x hs hu ho hi
  simp only [valuePullback, map_smul] at hs hu
  simp only [Pi.smul_apply] at hi ho
  rw [hs, hi, ho, hu]
  exact smul_comm _ _ _

theorem affineState_one_zero (u : EnergyState) : affineState (by norm_num : (0:ℝ)<1) 0 u = u := by
  apply energyValue_injective
  apply Lp.ext
  filter_upwards [affineState_value_ae (by norm_num : (0:ℝ)<1) 0 u] with x hx
  simpa only [valuePullback, Real.sqrt_one, affine, one_smul, add_zero] using hx

theorem affineState_comp {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (b d : Space) (u : EnergyState) :
    affineState ha b (affineState hc d u) = affineState (mul_pos hc ha) (c • b+d) u := by
  apply energyValue_injective
  apply Lp.ext
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae (affineState_value_ae hc d u)
  filter_upwards [affineState_value_ae ha b (affineState hc d u),
    affineState_value_ae (mul_pos hc ha) (c • b+d) u, hi] with x ho hr hi
  simp only [valuePullback] at ho hr hi
  rw [ho, hi, hr, smul_smul]
  have hs : Real.sqrt a * Real.sqrt c = Real.sqrt (c*a) := by
    rw [Real.sqrt_mul hc.le]; ring
  rw [hs]
  congr 2
  simp [affine, smul_add, smul_smul, add_assoc]

theorem affineState_right_inverse {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    affineState ha b (affineState (inv_pos.mpr ha) (-(a⁻¹ • b)) u) = u := by
  have h := affineState_comp ha (inv_pos.mpr ha) b (-(a⁻¹ • b)) u
  simpa only [inv_mul_cancel₀ ha.ne', add_neg_cancel, affineState_one_zero] using h

theorem affineState_left_inverse {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    affineState (inv_pos.mpr ha) (-(a⁻¹ • b)) (affineState ha b u) = u := by
  have h := affineState_comp (inv_pos.mpr ha) ha (-(a⁻¹ • b)) b u
  simpa only [mul_inv_cancel₀ ha.ne', smul_neg, smul_smul, one_smul,
    neg_add_cancel, affineState_one_zero] using h

/-- The same normed EnergyState is used, without introducing a rescaled norm instance. -/
def affineStateEquiv {a : ℝ} (ha : 0 < a) (b : Space) : EnergyState ≃ₗᵢ[ℂ] EnergyState where
  toFun := affineState ha b
  invFun := affineState (inv_pos.mpr ha) (-(a⁻¹ • b))
  left_inv := affineState_left_inverse ha b
  right_inv := affineState_right_inverse ha b
  map_add' := affineState_add ha b
  map_smul' := affineState_smul ha b
  norm_map' := affineState_norm ha b

/-- The paper convention T_(lambda,y)f(x)=lambda^(-1/2) f((x-y)/lambda). -/
def criticalAffineState (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) : EnergyState ≃ₗᵢ[ℂ] EnergyState :=
  affineStateEquiv (inv_pos.mpr hlambda) (-(lambda⁻¹ • y))

theorem criticalAffineState_value_ae (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (u : EnergyState) :
    (energyValue (criticalAffineState lambda hlambda y u) : Space → ℂ) =ᵐ[volume]
      (fun x => (Real.sqrt lambda)⁻¹ • energyValue u (lambda⁻¹ • (x-y))) := by
  filter_upwards [affineState_value_ae (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u] with x hx
  change energyValue (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u) x = _
  simpa only [valuePullback, affine, Real.sqrt_inv, sub_eq_add_neg, smul_add, smul_neg] using hx

theorem criticalAffineState_gradient_ae (lambda : ℝ) (hlambda : 0 < lambda) (y : Space)
    (u : EnergyState) (j : Fin 3) :
    (energyGradient j (criticalAffineState lambda hlambda y u) : Space → ℂ) =ᵐ[volume]
      (fun x => (lambda⁻¹ * (Real.sqrt lambda)⁻¹) • energyGradient j u (lambda⁻¹ • (x-y))) := by
  filter_upwards [affineState_gradient_ae (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u j] with x hx
  change energyGradient j (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u) x = _
  simpa only [gradientPullback, affine, Real.sqrt_inv, sub_eq_add_neg, smul_add, smul_neg] using hx

theorem criticalAffineState_gradientSquared (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (u : EnergyState) :
    gradientSquared (criticalAffineState lambda hlambda y u) = gradientSquared u :=
  affineState_gradientSquared (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u

theorem criticalAffineState_pureGradientNorm (lambda : ℝ) (hlambda : 0 < lambda)
    (y : Space) (u : EnergyState) :
    pureGradientNorm (criticalAffineState lambda hlambda y u) = pureGradientNorm u :=
  affineState_pureGradientNorm (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u

theorem criticalAffineState_interaction {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (u : EnergyState) :
    interactionLp α (energyValue (criticalAffineState lambda hlambda y u)) = interactionLp α (energyValue u) :=
  affineState_interaction hH (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u

theorem criticalAffineState_totalEnergy {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (u : EnergyState) :
    totalEnergy α (criticalAffineState lambda hlambda y u) = totalEnergy α u :=
  affineState_totalEnergy hH (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u

/-- Both original strict W thresholds are retained literally. -/
theorem criticalAffineState_below_W_iff {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    (lambda : ℝ) (hlambda : 0 < lambda) (y : Space) (u : EnergyState) :
    (gradientSquared (criticalAffineState lambda hlambda y u) < gradientSquared (normalizedBubbleState α) ∧
      totalEnergy α (criticalAffineState lambda hlambda y u) < totalEnergy α (normalizedBubbleState α)) ↔
    (gradientSquared u < gradientSquared (normalizedBubbleState α) ∧
      totalEnergy α u < totalEnergy α (normalizedBubbleState α)) := by
  rw [criticalAffineState_gradientSquared, criticalAffineState_totalEnergy hH]

#print axioms affineState_add
#print axioms affineState_smul
#print axioms affineState_comp
#print axioms affineStateEquiv
#print axioms criticalAffineState
#print axioms criticalAffineState_value_ae
#print axioms criticalAffineState_gradient_ae
#print axioms criticalAffineState_gradientSquared
#print axioms criticalAffineState_pureGradientNorm
#print axioms criticalAffineState_interaction
#print axioms criticalAffineState_totalEnergy
#print axioms criticalAffineState_below_W_iff
end HartreeF.CriticalAffine
