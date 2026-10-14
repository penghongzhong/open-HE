import FCompactCrossSeparatedTerms
import FCompactCrossSpatialScale

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open CriticalAffine AffineMixed

def separationBudget (c A B : ℝ) (S T : Set Space) (I : Set ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c*A*(volume S).toReal*B) * volume T ^ (5/6 : ℝ) * volume I ^ (1/2 : ℝ)

theorem separationBudget_ne_top (c A B : ℝ) {S T : Set Space} {I : Set ℝ}
    (hT : volume T ≠ ∞) (hI : volume I ≠ ∞) : separationBudget c A B S T I ≠ ∞ := by
  unfold separationBudget
  finiteness

theorem separationBudget_coeff {d : ℝ} (hd : 0 ≤ d) (c A B : ℝ)
    (S T : Set Space) (I : Set ℝ) :
    separationBudget (d*c) A B S T I = ENNReal.ofReal d * separationBudget c A B S T I := by
  unfold separationBudget
  rw [show d*c*A*(volume S).toReal*B=d*(c*A*(volume S).toReal*B) by ring,
    ENNReal.ofReal_mul hd]
  ring

/-- The exact support/amplitude budget under independent space and time scalings. -/
theorem separationBudget_scale {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (p q : ℝ) (y z : Space) (e : ℝ) {S T : Set Space} {I : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hI : MeasurableSet I)
    (c A B : ℝ) :
    separationBudget c (a^p*A) (b^q*B) ((affine a y) ⁻¹' S) ((affine b z) ⁻¹' T)
      ((timeAffine t e) ⁻¹' I) =
      ENNReal.ofReal (a^(p-3)*b^(q-5/2)*t^(-1 : ℝ)) * separationBudget c A B S T I := by
  have hai : (a^3)⁻¹ = a^(-3 : ℝ) := by rw [Real.rpow_neg ha.le]; norm_num
  unfold separationBudget
  rw [affine_preimage_volume ha y hS,affine_preimage_volume hb z hT,timeAffine_preimage_volume ht e hI,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_pos.mpr (pow_pos ha 3)).le,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 5/6),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    jacobian_rpow hb 3,jacobian_rpow ht 2]
  have hreal : c*(a^p*A)*((a^3)⁻¹*(volume S).toReal)*(b^q*B) =
      (a^(p-3)*b^q)*(c*A*(volume S).toReal*B) := by
    rw [hai,sub_eq_add_neg,Real.rpow_add ha]
    ring
  rw [hreal,ENNReal.ofReal_mul (by positivity : 0 ≤ a^(p-3)*b^q)]
  have hfactor : ENNReal.ofReal (a^(p-3)*b^q) * ENNReal.ofReal (b^(-(3:ℝ)*(5/6))) *
      ENNReal.ofReal (t^(-(2:ℝ)*(1/2))) = ENNReal.ofReal (a^(p-3)*b^(q-5/2)*t^(-1 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ a^(p-3)*b^q),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (a^(p-3)*b^q)*b^(-(3:ℝ)*(5/6)))]
    congr 1
    rw [show q-5/2=q+(-(3:ℝ)*(5/6)) by ring,Real.rpow_add hb,
      show -(2:ℝ)*(1/2)=(-1:ℝ) by norm_num]
    ring
  calc
    _ = (ENNReal.ofReal (a^(p-3)*b^q) * ENNReal.ofReal (b^(-(3:ℝ)*(5/6))) *
        ENNReal.ofReal (t^(-(2:ℝ)*(1/2)))) *
      (ENNReal.ofReal (c*A*(volume S).toReal*B)*volume T^(5/6:ℝ)*volume I^(1/2:ℝ)) := by ring
    _ = _ := by rw [hfactor]

theorem separated_inner_scale_identity {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (α : ℝ) :
    (a^((5+α)/2-3)*b^((2+α)/2-5/2)*a^(-1 : ℝ))*D^(α-3) =
      (D*Real.sqrt (a*b))^(α-3) := by
  rw [Real.mul_rpow hD.le (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,
    ← Real.rpow_mul (mul_pos ha hb).le,Real.mul_rpow ha.le hb.le]
  have hbexp : (2+α)/2-5/2=(1/2:ℝ)*(α-3) := by ring
  have haexp : (1/2:ℝ)*(α-3)=((5+α)/2-3)+(-1) := by ring
  rw [hbexp,haexp,Real.rpow_add ha]
  ring

theorem separated_outer_scale_identity {a b D : ℝ} (ha : 0 < a) (hb : 0 < b) (hD : 0 < D)
    (α : ℝ) :
    (a^((3+α)/2-3)*b^((4+α)/2-5/2)*b^(-1 : ℝ))*D^(α-3) =
      (D*Real.sqrt (a*b))^(α-3) := by
  rw [Real.mul_rpow hD.le (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,
    ← Real.rpow_mul (mul_pos ha hb).le,Real.mul_rpow ha.le hb.le]
  have haexp : (3+α)/2-3=(1/2:ℝ)*(α-3) := by ring
  have hbexp : (1/2:ℝ)*(α-3)=((4+α)/2-5/2)+(-1) := by ring
  rw [haexp,hbexp,Real.rpow_add hb]
  ring

#print axioms separationBudget_ne_top
#print axioms separationBudget_coeff
#print axioms separationBudget_scale
#print axioms separated_inner_scale_identity
#print axioms separated_outer_scale_identity
end HartreeF.CompactCross
