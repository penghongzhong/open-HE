import FActualL6MassGauge

/-! Exact open-ball mass transport for the existing actual affine state.
This source is UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace HartreeF.L6OrbitGauge
open EnergySpace CriticalAffine

private theorem affine_mem_ball_iff {a : ℝ} (ha : 0 < a) (b x z : Space) (R : ℝ) :
    affine a b z ∈ ball (affine a b x) (a*R) ↔ z ∈ ball x R := by
  have he : affine a b z - affine a b x = a • (z-x) := by
    simp only [affine, smul_sub]
    abel
  simp only [mem_ball, dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  exact mul_lt_mul_iff_right₀ ha

/-- The local formula uses the actual affine representative, with its AE identity first. -/
theorem ballMass_affineState {a : ℝ} (ha : 0 < a) (b : Space)
    (u : EnergyState) (x : Space) (R : ℝ) :
    ballMass (affineState ha b u) x R = ballMass u (a • x+b) (a*R) := by
  have hpow : (Real.sqrt a)^6 = a^3 := by
    rw [show (6:ℕ)=2*3 by norm_num, pow_mul, Real.sq_sqrt ha.le]
  have hpoint (z : Space) :
      (ball x R).indicator (fun w => ‖valuePullback a b (energyValue u) w‖^6) z =
      a^3 * (ball (affine a b x) (a*R)).indicator
        (fun w => ‖energyValue u w‖^6) (affine a b z) := by
    by_cases hz : z ∈ ball x R
    · have hza := (affine_mem_ball_iff ha b x z R).mpr hz
      simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hza,
        valuePullback, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg a), mul_pow, hpow]
    · have hza : affine a b z ∉ ball (affine a b x) (a*R) :=
        fun h => hz ((affine_mem_ball_iff ha b x z R).mp h)
      simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hza, mul_zero]
  change (∫ z in ball x R, ‖energyValue (affineState ha b u) z‖^6) =
    ∫ z in ball (affine a b x) (a*R), ‖energyValue u z‖^6
  rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
  calc
    _ = ∫ z, (ball x R).indicator
        (fun w => ‖valuePullback a b (energyValue u) w‖^6) z := by
      apply integral_congr_ae
      filter_upwards [affineState_value_ae ha b u] with z hz
      by_cases h : z ∈ ball x R
      · simp only [Set.indicator_of_mem h, hz]
      · simp only [Set.indicator_of_notMem h]
    _ = ∫ z, a^3 * (ball (affine a b x) (a*R)).indicator
        (fun w => ‖energyValue u w‖^6) (affine a b z) :=
      integral_congr_ae (ae_of_all _ hpoint)
    _ = _ := by
      rw [integral_const_mul, affine_integral ha b, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]

theorem mass_criticalAffine (lambda : ℝ) (hlambda : 0 < lambda)
    (y : Space) (v : EnergyState) :
    mass (criticalAffineState lambda hlambda y v) = mass v := by
  change ‖energyValue (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) v)‖^6 = _
  rw [affineState_value_norm, mass]

/-- The exact paper-convention transport law, without any boundary replacement. -/
theorem ballMass_criticalAffine (lambda : ℝ) (hlambda : 0 < lambda)
    (y : Space) (v : EnergyState) (x : Space) (R : ℝ) :
    ballMass (criticalAffineState lambda hlambda y v) x R =
      ballMass v (lambda⁻¹ • (x-y)) (R/lambda) := by
  change ballMass (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) v) x R = _
  rw [ballMass_affineState]
  congr 1
  · simp only [sub_eq_add_neg, smul_add, smul_neg]
  · ring

/-- Transport the selected ball and every half-radius center. -/
theorem gauge_criticalAffine_pullback {lambda : ℝ} (hlambda : 0 < lambda)
    (y : Space) {v : EnergyState} {R : ℝ} {x : Space}
    (h : Gauge (criticalAffineState lambda hlambda y v) R x) :
    Gauge v (R/lambda) (lambda⁻¹ • (x-y)) := by
  refine ⟨div_pos h.radius_pos hlambda, ?_, ?_⟩
  · simpa only [mass_criticalAffine, ballMass_criticalAffine] using h.lower
  · intro d
    have hd := h.half_upper (y + lambda • d)
    rw [mass_criticalAffine, ballMass_criticalAffine] at hd
    have hc : lambda⁻¹ • (y + lambda • d-y) = d := by
      simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlambda.ne', one_smul]
    have hr : (R/2)/lambda = (R/lambda)/2 := by ring
    simpa only [hc, hr] using hd

end HartreeF.L6OrbitGauge
