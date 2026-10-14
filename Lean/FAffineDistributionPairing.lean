import FAffineBilinearTests
import FAffineMixedNormIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.AffinePath
open EnergySpace CriticalAffine AffineMixed FreeFlow

theorem affineState_distribution {a : ℝ} (ha : 0<a) (b : Space) (u : EnergyState) (φ : FreeFlow.Test) :
    energyDistribution (affineState ha b u) φ=energyDistribution u (dualAffineTest ha b φ) := by
  change Lp.toTemperedDistribution (energyValue (affineState ha b u)) φ=
    Lp.toTemperedDistribution (energyValue u) (dualAffineTest ha b φ)
  simp only [Lp.toTemperedDistribution_apply,smul_eq_mul]
  calc
    _ = ∫ x, φ x*valuePullback a b (energyValue u) x := by
      apply integral_congr_ae
      filter_upwards [affineState_value_ae ha b u] with x hx
      rw [hx]
    _ = _ := valuePullback_pairing ha b (energyValue u) φ

/-- The scalar forcing amplitude is a^2 times the homogeneous value action. -/
theorem parabolicSource_valuePullback {a : ℝ} (ha : 0<a) (b : Space) (c : ℝ)
    (e : ℝ → Space → ℂ) (t : ℝ) (x : Space) :
    parabolicField a b c (5/2) e t x=a^2 • valuePullback a b (e (timeAffine a c t)) x := by
  have hk : a^2*Real.sqrt a=a^(5/2:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = a^(2:ℝ)*a^(1/2:ℝ) := by rw [Real.rpow_two]
      _ = _ := by rw [← Real.rpow_add ha]; norm_num
  simp only [parabolicField,valuePullback,smul_smul,hk]

theorem parabolicSource_spatial_pairing {a : ℝ} (ha : 0<a) (b : Space) (c : ℝ)
    (e : ℝ → Space → ℂ) (t : ℝ) (φ : FreeFlow.Test) :
    (∫ x, φ x*parabolicField a b c (5/2) e t x)=
      a^2 • ∫ y, dualAffineTest ha b φ y*e (timeAffine a c t) y := by
  simp_rw [parabolicSource_valuePullback ha b c e t]
  calc
    _ = a^2 • ∫ x, φ x*valuePullback a b (e (timeAffine a c t)) x := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Complex.real_smul]
      ring
    _ = _ := congrArg (fun z : ℂ => a^2 • z)
      (valuePullback_pairing ha b (e (timeAffine a c t)) φ)

#print axioms affineState_distribution
#print axioms parabolicSource_valuePullback
#print axioms parabolicSource_spatial_pairing
end HartreeF.AffinePath
