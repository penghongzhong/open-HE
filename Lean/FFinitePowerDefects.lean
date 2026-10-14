import FPowerMixedRemainders
import FActualPowerMixedRemainders
import Mathlib.Algebra.BigOperators.Fin

/-!
Finite-family, pointwise Hartree power defects. Author draft, UNCOMPILED.

The finite telescope uses the genuine two-input remainders. The derivative
estimate first expands the genuine real-linear derivative in its direction,
then keeps every off-diagonal value/direction label. All sums are finite, all
constants are independent of their cardinality, and no division by the radius
is used. In particular real-rpow totalization is respected at radius zero.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace HartreeF.FinitePowerDefects

open WeakHartreeChain

variable {ι : Type*} [DecidableEq ι]

/-- Sum of the actual pointwise profile norms. -/
def radius (s : Finset ι) (u : ι → ℂ) : ℝ := ∑ i ∈ s, ‖u i‖

/-- Ordered, off-diagonal value pairs, including their fractional powers. -/
def pairSum (s : Finset ι) (u : ι → ℂ) (δ : ℝ) : ℝ :=
  ∑ j ∈ s, ∑ i ∈ s.erase j, (‖u i‖ * ‖u j‖) ^ δ

/-- The direction label is `j`; it is never replaced by the value label `i`. -/
def directionSum (s : Finset ι) (u h : ι → ℂ) : ℝ :=
  ∑ j ∈ s, ∑ i ∈ s.erase j, ‖u i‖ * ‖h j‖

def densityDefect (α : ℝ) (s : Finset ι) (u : ι → ℂ) : ℝ :=
  WeakHartreeChain.density (3 + α) (∑ i ∈ s, u i) - ∑ i ∈ s, WeakHartreeChain.density (3 + α) (u i)

def localDefect (α : ℝ) (s : Finset ι) (u : ι → ℂ) : ℂ :=
  localFactor (1 + α) (∑ i ∈ s, u i) - ∑ i ∈ s, localFactor (1 + α) (u i)

def densityDerivativeDefect (α : ℝ) (s : Finset ι) (u h : ι → ℂ) : ℝ :=
  densityDerivative (3 + α) (∑ i ∈ s, u i) (∑ i ∈ s, h i) -
    ∑ i ∈ s, densityDerivative (3 + α) (u i) (h i)

def localDerivativeDefect (α : ℝ) (s : Finset ι) (u h : ι → ℂ) : ℂ :=
  localFactorDerivative (1 + α) (∑ i ∈ s, u i) (∑ i ∈ s, h i) -
    ∑ i ∈ s, localFactorDerivative (1 + α) (u i) (h i)

omit [DecidableEq ι] in
theorem radius_nonneg (s : Finset ι) (u : ι → ℂ) : 0 ≤ radius s u :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem pairSum_nonneg (s : Finset ι) (u : ι → ℂ) (δ : ℝ) :
    0 ≤ pairSum s u δ :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _))

theorem directionSum_nonneg (s : Finset ι) (u h : ι → ℂ) :
    0 ≤ directionSum s u h :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _)))

omit [DecidableEq ι] in
theorem norm_le_radius {s : Finset ι} (u : ι → ℂ) {i : ι} (hi : i ∈ s) :
    ‖u i‖ ≤ radius s u :=
  Finset.single_le_sum (fun _ _ => norm_nonneg _) hi

omit [DecidableEq ι] in
theorem norm_sum_le_radius (s : Finset ι) (u : ι → ℂ) :
    ‖∑ i ∈ s, u i‖ ≤ radius s u := norm_sum_le s u

omit [DecidableEq ι] in
@[simp] theorem radius_empty (u : ι → ℂ) : radius ∅ u = 0 := by simp [radius]

@[simp] theorem radius_insert {s : Finset ι} {a : ι} (ha : a ∉ s) (u : ι → ℂ) :
    radius (insert a s) u = ‖u a‖ + radius s u := by
  simp only [radius, Finset.sum_insert ha]

@[simp] theorem pairSum_empty (u : ι → ℂ) (δ : ℝ) : pairSum ∅ u δ = 0 := by
  simp [pairSum]

@[simp] theorem pairSum_singleton (a : ι) (u : ι → ℂ) (δ : ℝ) :
    pairSum {a} u δ = 0 := by simp [pairSum]

@[simp] theorem directionSum_empty (u h : ι → ℂ) : directionSum ∅ u h = 0 := by
  simp [directionSum]

@[simp] theorem directionSum_singleton (a : ι) (u h : ι → ℂ) :
    directionSum {a} u h = 0 := by simp [directionSum]

private theorem pairSum_one_eq (s : Finset ι) (u : ι → ℂ) :
    pairSum s u 1 = (radius s u) ^ 2 - ∑ i ∈ s, ‖u i‖ ^ 2 := by
  unfold pairSum
  simp only [Real.rpow_one, ← Finset.sum_mul]
  calc
    (∑ j ∈ s, (∑ i ∈ s.erase j, ‖u i‖) * ‖u j‖) =
        ∑ j ∈ s, (radius s u - ‖u j‖) * ‖u j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [radius] using congrArg (fun r : ℝ => r * ‖u j‖)
        (Finset.sum_erase_eq_sub (s := s) (f := fun i => ‖u i‖) hj)
    _ = radius s u * (∑ j ∈ s, ‖u j‖) - ∑ j ∈ s, ‖u j‖ ^ 2 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, pow_two]
    _ = (radius s u) ^ 2 - ∑ i ∈ s, ‖u i‖ ^ 2 := by
      change radius s u * radius s u - _ = _
      ring

private theorem pairSum_one_insert {s : Finset ι} {a : ι} (ha : a ∉ s)
    (u : ι → ℂ) :
    pairSum (insert a s) u 1 = pairSum s u 1 + 2 * ‖u a‖ * radius s u := by
  simp only [pairSum_one_eq, radius, Finset.sum_insert ha]
  ring

/-- The only generic value hypothesis is the already-proved two-input bound.
The finite-family conclusion is produced by induction, not assumed. -/
private theorem finite_value_bound
    {G : Type*} [NormedAddCommGroup G] {F : ℂ → G} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hzero : F 0 = 0)
    (hbinary : ∀ a b : ℂ, ‖F (a + b) - F a - F b‖ ≤
      C * ‖a‖ * ‖b‖ * (‖a‖ + ‖b‖) ^ t)
    (s : Finset ι) (u : ι → ℂ) :
    ‖F (∑ i ∈ s, u i) - ∑ i ∈ s, F (u i)‖ ≤
      C * (radius s u) ^ t * pairSum s u 1 := by
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | @insert a s ha ih =>
      have hR : 0 ≤ radius s u := radius_nonneg s u
      have hRT : 0 ≤ radius (insert a s) u := radius_nonneg _ u
      have hsmall : radius s u ≤ radius (insert a s) u := by
        rw [radius_insert ha]
        exact le_add_of_nonneg_left (norm_nonneg _)
      have hweight : (radius s u) ^ t ≤ (radius (insert a s) u) ^ t :=
        Real.rpow_le_rpow hR hsmall ht
      have hi : ‖F (∑ i ∈ s, u i) - ∑ i ∈ s, F (u i)‖ ≤
          C * (radius (insert a s) u) ^ t * pairSum s u 1 :=
        ih.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hweight hC) (pairSum_nonneg s u 1))
      have hsum := norm_sum_le_radius s u
      have hrad : ‖u a‖ + ‖∑ i ∈ s, u i‖ ≤ radius (insert a s) u := by
        rw [radius_insert ha]
        exact add_le_add le_rfl hsum
      have hpow : (‖u a‖ + ‖∑ i ∈ s, u i‖) ^ t ≤
          (radius (insert a s) u) ^ t :=
        Real.rpow_le_rpow (add_nonneg (norm_nonneg _) (norm_nonneg _)) hrad ht
      have hb : ‖F (u a + ∑ i ∈ s, u i) - F (u a) - F (∑ i ∈ s, u i)‖ ≤
          C * (radius (insert a s) u) ^ t * (‖u a‖ * radius s u) := by
        calc
          _ ≤ C * ‖u a‖ * ‖∑ i ∈ s, u i‖ * (‖u a‖ + ‖∑ i ∈ s, u i‖) ^ t :=
            hbinary _ _
          _ ≤ C * ‖u a‖ * radius s u * (radius (insert a s) u) ^ t := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (norm_nonneg _)))
              hpow (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _)
              (mul_nonneg (mul_nonneg hC (norm_nonneg _)) hR)
          _ = _ := by ring
      have hdecomp : F (∑ i ∈ insert a s, u i) - ∑ i ∈ insert a s, F (u i) =
          (F (u a + ∑ i ∈ s, u i) - F (u a) - F (∑ i ∈ s, u i)) +
          (F (∑ i ∈ s, u i) - ∑ i ∈ s, F (u i)) := by
        simp only [Finset.sum_insert ha]
        abel
      have hpairs : ‖u a‖ * radius s u + pairSum s u 1 ≤
          pairSum (insert a s) u 1 := by
        rw [pairSum_one_insert ha]
        nlinarith [mul_nonneg (norm_nonneg (u a)) hR]
      rw [hdecomp]
      calc
        _ ≤ ‖F (u a + ∑ i ∈ s, u i) - F (u a) - F (∑ i ∈ s, u i)‖ +
            ‖F (∑ i ∈ s, u i) - ∑ i ∈ s, F (u i)‖ := norm_add_le _ _
        _ ≤ C * (radius (insert a s) u) ^ t * (‖u a‖ * radius s u) +
            C * (radius (insert a s) u) ^ t * pairSum s u 1 := add_le_add hb hi
        _ = C * (radius (insert a s) u) ^ t *
            (‖u a‖ * radius s u + pairSum s u 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpairs
          (mul_nonneg hC (Real.rpow_nonneg hRT _))

/-- Real linearity separates all direction labels before applying a genuine
first-derivative difference estimate. No second derivative is assumed. -/
private theorem finite_derivative_bound
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {DF : ℂ → ℂ →L[ℝ] G} {K t : ℝ} (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hdiff : ∀ a b : ℂ, ‖DF a - DF b‖ ≤ K * (‖a‖ + ‖b‖) ^ t * ‖a - b‖)
    (s : Finset ι) (u h : ι → ℂ) :
    ‖DF (∑ i ∈ s, u i) (∑ i ∈ s, h i) - ∑ i ∈ s, DF (u i) (h i)‖ ≤
      (K * (2 : ℝ) ^ t) * (radius s u) ^ t * directionSum s u h := by
  have hR := radius_nonneg s u
  have he : DF (∑ i ∈ s, u i) (∑ i ∈ s, h i) - ∑ i ∈ s, DF (u i) (h i) =
      ∑ j ∈ s, (DF (∑ i ∈ s, u i) - DF (u j)) (h j) := by
    rw [map_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [sub_apply]
  have hterm (j : ι) (hj : j ∈ s) :
      ‖(DF (∑ i ∈ s, u i) - DF (u j)) (h j)‖ ≤
        (K * (2 : ℝ) ^ t) * (radius s u) ^ t *
          (∑ i ∈ s.erase j, ‖u i‖ * ‖h j‖) := by
    have hrad : ‖∑ i ∈ s, u i‖ + ‖u j‖ ≤ 2 * radius s u := by
      have h1 := norm_sum_le_radius s u
      have h2 := norm_le_radius u hj
      linarith
    have hpow := Real.rpow_le_rpow
      (add_nonneg (norm_nonneg (∑ i ∈ s, u i)) (norm_nonneg (u j))) hrad ht
    have hrest : (∑ i ∈ s, u i) - u j = ∑ i ∈ s.erase j, u i :=
      (Finset.sum_erase_eq_sub hj).symm
    have hdist : ‖(∑ i ∈ s, u i) - u j‖ ≤ ∑ i ∈ s.erase j, ‖u i‖ := by
      rw [hrest]
      exact norm_sum_le _ _
    calc
      _ ≤ ‖DF (∑ i ∈ s, u i) - DF (u j)‖ * ‖h j‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * (‖∑ i ∈ s, u i‖ + ‖u j‖) ^ t *
          ‖(∑ i ∈ s, u i) - u j‖) * ‖h j‖ :=
        mul_le_mul_of_nonneg_right (hdiff _ _) (norm_nonneg _)
      _ ≤ (K * (2 * radius s u) ^ t * (∑ i ∈ s.erase j, ‖u i‖)) * ‖h j‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hK) hdist
          (norm_nonneg _) (mul_nonneg hK (Real.rpow_nonneg (mul_nonneg (by norm_num) hR) _))
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR, ← Finset.sum_mul]
        ring
  rw [he]
  calc
    _ ≤ ∑ j ∈ s, ‖(DF (∑ i ∈ s, u i) - DF (u j)) (h j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, (K * (2 : ℝ) ^ t) * (radius s u) ^ t *
        (∑ i ∈ s.erase j, ‖u i‖ * ‖h j‖) := Finset.sum_le_sum hterm
    _ = _ := by simp only [directionSum, Finset.mul_sum]

/-- Fractional extraction of a pair, valid also when `R = 0` and when the
remaining exponent is zero. -/
private theorem fractional_pair_bound {R x t δ : ℝ}
    (hR : 0 ≤ R) (hx : 0 ≤ x) (hxR : x ≤ R ^ 2)
    (ht : 0 ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    R ^ t * x ≤ R ^ (t + 2 - 2 * δ) * x ^ δ := by
  have hd : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  have hxpow : x = x ^ δ * x ^ (1 - δ) := by
    rw [← Real.rpow_add_of_nonneg hx hδ.le hd,
      show δ + (1 - δ) = 1 by ring, Real.rpow_one]
  have hxp : x ^ (1 - δ) ≤ R ^ (2 * (1 - δ)) := by
    calc
      _ ≤ (R ^ 2) ^ (1 - δ) := Real.rpow_le_rpow hx hxR hd
      _ = _ := by rw [← Real.rpow_two R, ← Real.rpow_mul hR]
  calc
    R ^ t * x = R ^ t * (x ^ δ * x ^ (1 - δ)) := by rw [← hxpow]
    _ ≤ R ^ t * (x ^ δ * R ^ (2 * (1 - δ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxp (Real.rpow_nonneg hx _)) (Real.rpow_nonneg hR _)
    _ = (R ^ t * R ^ (2 * (1 - δ))) * x ^ δ := by ring
    _ = R ^ (t + 2 - 2 * δ) * x ^ δ := by
      rw [← Real.rpow_add_of_nonneg hR ht (mul_nonneg (by norm_num) hd)]
      congr 2
      ring

private theorem fractional_pairSum_bound {t δ : ℝ}
    (ht : 0 ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (u : ι → ℂ) :
    (radius s u) ^ t * pairSum s u 1 ≤
      (radius s u) ^ (t + 2 - 2 * δ) * pairSum s u δ := by
  simp only [pairSum, Real.rpow_one, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ∈ s := (Finset.mem_erase.mp hi).2
  apply fractional_pair_bound (radius_nonneg s u)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ ht hδ hδ1
  calc
    ‖u i‖ * ‖u j‖ ≤ radius s u * radius s u :=
      mul_le_mul (norm_le_radius u hi') (norm_le_radius u hj)
        (norm_nonneg _) (radius_nonneg s u)
    _ = _ := by ring

/-- Finite density value defect, for every `α > 0`. -/
theorem densityDefect_bound {α : ℝ} (hα : 0 < α) (s : Finset ι) (u : ι → ℂ) :
    ‖densityDefect α s u‖ ≤
      densityMixedConstant (3 + α) * (radius s u) ^ (1 + α) * pairSum s u 1 := by
  have hp : 3 < 3 + α := by linarith
  simpa only [densityDefect, show 3 + α - 2 = 1 + α by ring] using
    finite_value_bound (densityMixedConstant_pos hp).le (by linarith : 0 ≤ (3 + α) - 2)
      (show WeakHartreeChain.density (3 + α) 0 = 0 by
        simp [WeakHartreeChain.density, Real.zero_rpow (show 3 + α ≠ 0 by linarith)])
      (density_mixed_remainder_bound hp) s u

/-- Finite local-factor value defect, including `0 < α < 1`. -/
theorem localDefect_bound {α : ℝ} (hα : 0 < α) (s : Finset ι) (u : ι → ℂ) :
    ‖localDefect α s u‖ ≤
      localFactorMixedConstant (1 + α) * (radius s u) ^ α * pairSum s u 1 := by
  have hq : 1 < 1 + α := by linarith
  simpa only [localDefect, show 1 + α - 1 = α by ring] using
    finite_value_bound (localFactorMixedConstant_pos hq).le (by linarith : 0 ≤ (1 + α) - 1)
      (show localFactor (1 + α) 0 = 0 by simp [localFactor])
      (localFactor_mixed_remainder_bound hq) s u

theorem densityDefect_fractional_bound {α δ : ℝ} (hα : 0 < α)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (u : ι → ℂ) :
    ‖densityDefect α s u‖ ≤ densityMixedConstant (3 + α) *
      (radius s u) ^ (3 + α - 2 * δ) * pairSum s u δ := by
  have hc := (densityMixedConstant_pos (show 3 < 3 + α by linarith)).le
  calc
    _ ≤ densityMixedConstant (3 + α) * (radius s u) ^ (1 + α) * pairSum s u 1 :=
      densityDefect_bound hα s u
    _ ≤ densityMixedConstant (3 + α) *
        ((radius s u) ^ ((1 + α) + 2 - 2 * δ) * pairSum s u δ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (fractional_pairSum_bound (by linarith : 0 ≤ 1 + α) hδ hδ1 s u) hc
    _ = _ := by rw [show (1 + α) + 2 - 2 * δ = 3 + α - 2 * δ by ring]; ring

theorem localDefect_fractional_bound {α δ : ℝ} (hα : 0 < α)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (s : Finset ι) (u : ι → ℂ) :
    ‖localDefect α s u‖ ≤ localFactorMixedConstant (1 + α) *
      (radius s u) ^ (2 + α - 2 * δ) * pairSum s u δ := by
  have hc := (localFactorMixedConstant_pos (show 1 < 1 + α by linarith)).le
  calc
    _ ≤ localFactorMixedConstant (1 + α) * (radius s u) ^ α * pairSum s u 1 :=
      localDefect_bound hα s u
    _ ≤ localFactorMixedConstant (1 + α) *
        ((radius s u) ^ (α + 2 - 2 * δ) * pairSum s u δ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (fractional_pairSum_bound hα.le hδ hδ1 s u) hc
    _ = _ := by rw [show α + 2 - 2 * δ = 2 + α - 2 * δ by ring]; ring

/-- Every ordered off-diagonal value/direction product is retained. -/
theorem densityDerivativeDefect_bound {α : ℝ} (hα : 0 < α)
    (s : Finset ι) (u h : ι → ℂ) :
    ‖densityDerivativeDefect α s u h‖ ≤ densityMixedConstant (3 + α) *
      (radius s u) ^ (1 + α) * directionSum s u h := by
  simpa only [densityDerivativeDefect, densityMixedConstant,
    show (3 + α) - 2 = 1 + α by ring] using
    finite_derivative_bound
      (mul_nonneg (by linarith : 0 ≤ 3 + α) (by linarith : 0 ≤ (3 + α) - 1))
      (by linarith : 0 ≤ (3 + α) - 2)
      (densityDerivative_difference_bound (show 3 < 3 + α by linarith)) s u h

/-- This is the derivative of the true noninteger local factor. -/
theorem localDerivativeDefect_bound {α : ℝ} (hα : 0 < α)
    (s : Finset ι) (u h : ι → ℂ) :
    ‖localDerivativeDefect α s u h‖ ≤ localFactorMixedConstant (1 + α) *
      (radius s u) ^ α * directionSum s u h := by
  simpa only [localDerivativeDefect, localFactorMixedConstant,
    show (1 + α) - 1 = α by ring] using
    finite_derivative_bound
      (mul_nonneg (by linarith : 0 ≤ 1 + α) (by linarith : 0 ≤ (1 + α) + 5))
      (by linarith : 0 ≤ (1 + α) - 1)
      (localFactorDerivative_difference_bound (show 1 < 1 + α by linarith)) s u h

/-! Empty, singleton, and padded-zero families are literal special cases. -/

omit [DecidableEq ι] in
@[simp] theorem densityDefect_empty {α : ℝ} (hα : 0 < α) (u : ι → ℂ) :
    densityDefect α ∅ u = 0 := by
  simp [densityDefect, WeakHartreeChain.density, Real.zero_rpow (show 3 + α ≠ 0 by linarith)]

omit [DecidableEq ι] in
@[simp] theorem localDefect_empty (α : ℝ) (u : ι → ℂ) : localDefect α ∅ u = 0 := by
  simp [localDefect, localFactor]

omit [DecidableEq ι] in
@[simp] theorem densityDerivativeDefect_empty (α : ℝ) (u h : ι → ℂ) :
    densityDerivativeDefect α ∅ u h = 0 := by simp [densityDerivativeDefect]

omit [DecidableEq ι] in
@[simp] theorem localDerivativeDefect_empty (α : ℝ) (u h : ι → ℂ) :
    localDerivativeDefect α ∅ u h = 0 := by simp [localDerivativeDefect]

omit [DecidableEq ι] in
@[simp] theorem densityDefect_singleton (α : ℝ) (a : ι) (u : ι → ℂ) :
    densityDefect α {a} u = 0 := by simp [densityDefect]

omit [DecidableEq ι] in
@[simp] theorem localDefect_singleton (α : ℝ) (a : ι) (u : ι → ℂ) :
    localDefect α {a} u = 0 := by simp [localDefect]

omit [DecidableEq ι] in
@[simp] theorem densityDerivativeDefect_singleton (α : ℝ) (a : ι) (u h : ι → ℂ) :
    densityDerivativeDefect α {a} u h = 0 := by simp [densityDerivativeDefect]

omit [DecidableEq ι] in
@[simp] theorem localDerivativeDefect_singleton (α : ℝ) (a : ι) (u h : ι → ℂ) :
    localDerivativeDefect α {a} u h = 0 := by simp [localDerivativeDefect]

/-- Zero value padding changes neither literal value defect. -/
theorem valueDefects_insert_zero {α : ℝ} (hα : 0 < α) {s : Finset ι} {a : ι}
    (ha : a ∉ s) (u : ι → ℂ) (hu : u a = 0) :
    densityDefect α (insert a s) u = densityDefect α s u ∧
      localDefect α (insert a s) u = localDefect α s u := by
  simp [densityDefect, localDefect, Finset.sum_insert ha, hu, WeakHartreeChain.density, localFactor,
    Real.zero_rpow (show 3 + α ≠ 0 by linarith)]

/-- A padded profile has both value and direction zero; no unmatched direction
at a zero value is silently discarded. -/
theorem derivativeDefects_insert_zero (α : ℝ) {s : Finset ι} {a : ι}
    (ha : a ∉ s) (u h : ι → ℂ) (hu : u a = 0) (hh : h a = 0) :
    densityDerivativeDefect α (insert a s) u h = densityDerivativeDefect α s u h ∧
      localDerivativeDefect α (insert a s) u h = localDerivativeDefect α s u h := by
  simp [densityDerivativeDefect, localDerivativeDefect, Finset.sum_insert ha, hu, hh]

/-- Explicit empty finite-type witness, with the totalized density at zero. -/
theorem fin_zero_defects {α : ℝ} (hα : 0 < α) (u h : Fin 0 → ℂ) :
    densityDefect α Finset.univ u = 0 ∧ localDefect α Finset.univ u = 0 ∧
      densityDerivativeDefect α Finset.univ u h = 0 ∧
      localDerivativeDefect α Finset.univ u h = 0 := by
  simp [densityDefect, localDefect, densityDerivativeDefect, localDerivativeDefect,
    WeakHartreeChain.density, localFactor, Real.zero_rpow (show 3 + α ≠ 0 by linarith)]

/-- Explicit one-profile witness; no spurious self-interaction remains. -/
theorem fin_one_defects (α : ℝ) (u h : Fin 1 → ℂ) :
    densityDefect α Finset.univ u = 0 ∧ localDefect α Finset.univ u = 0 ∧
      densityDerivativeDefect α Finset.univ u h = 0 ∧
      localDerivativeDefect α Finset.univ u h = 0 := by
  simp only [densityDefect, localDefect, densityDerivativeDefect, localDerivativeDefect,
    Fin.sum_univ_one, sub_self, and_self]

#print axioms densityDefect_bound
#print axioms localDefect_bound
#print axioms densityDefect_fractional_bound
#print axioms localDefect_fractional_bound
#print axioms densityDerivativeDefect_bound
#print axioms localDerivativeDefect_bound
#print axioms valueDefects_insert_zero
#print axioms derivativeDefects_insert_zero
#print axioms fin_zero_defects
#print axioms fin_one_defects

end HartreeF.FinitePowerDefects
