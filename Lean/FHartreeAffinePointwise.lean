import FCriticalAffineEnergy

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.AffineForcing
open CriticalAffine ForcingDomain

/-- The actual nonlocal convolution transforms with the critical density power
and the exact 3D Jacobian. Positive a is the inverse paper length scale. -/
theorem potential_valuePullback (alpha c : ℝ) {a : ℝ} (ha : 0<a) (b : Space)
    (u : Space → ℂ) (x : Space) :
    potential alpha c (valuePullback a b u) x=
      a^((3-alpha)/2)*potential alpha c u (affine a b x) := by
  have hi (z : Space) :
      rieszKernel alpha c (x-z)*powerDensity alpha (valuePullback a b u) z=
      a^((9-alpha)/2)*(rieszKernel alpha c (affine a b x-affine a b z)*
        powerDensity alpha u (affine a b z)) := by
    rw [valuePullback_powerDensity alpha ha b, rieszKernel_affine_sub alpha c ha b]
    have hp : a^((9-alpha)/2)*a^(alpha-3)=a^((3+alpha)/2) := by
      rw [← Real.rpow_add ha]
      congr 1
      ring
    rw [← hp]
    ring
  unfold potential
  simp_rw [hi]
  rw [integral_const_mul, affine_integral ha b (fun z =>
    rieszKernel alpha c (affine a b x-z)*powerDensity alpha u z), smul_eq_mul, ← mul_assoc]
  congr 1
  rw [show (a^3)⁻¹=a^(-3:ℝ) by rw [Real.rpow_neg ha.le]; simp,
    ← Real.rpow_add ha]
  congr 1
  ring

/-- Exact local factor scaling for the original critical power p=3+alpha. -/
theorem localFactor_valuePullback (alpha : ℝ) {a : ℝ} (ha : 0<a) (b : Space)
    (u : Space → ℂ) (x : Space) :
    ForcingDomain.localFactor alpha (valuePullback a b u) x=
      a^((2+alpha)/2) • ForcingDomain.localFactor alpha u (affine a b x) := by
  simp only [ForcingDomain.localFactor, valuePullback, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg a), Real.mul_rpow (Real.sqrt_nonneg a) (norm_nonneg _)]
  rw [smul_smul, smul_smul]
  congr 1
  have hp : (Real.sqrt a)^(1+alpha)*Real.sqrt a=a^((2+alpha)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
    congr 1
    ring
  calc
    _ = ((Real.sqrt a)^(1+alpha)*Real.sqrt a)*‖u (affine a b x)‖^(1+alpha) := by ring
    _ = _ := by rw [hp]

/-- Literal Hartree forcing covariance, proved from the actual convolution. -/
theorem forcing_valuePullback (alpha c : ℝ) {a : ℝ} (ha : 0<a) (b : Space)
    (u : Space → ℂ) (x : Space) :
    forcing alpha c (valuePullback a b u) x=
      a^(5/2:ℝ) • forcing alpha c u (affine a b x) := by
  change potential alpha c (valuePullback a b u) x •
    ForcingDomain.localFactor alpha (valuePullback a b u) x=_
  rw [potential_valuePullback alpha c ha b, localFactor_valuePullback alpha ha b, smul_smul]
  change (a^((3-alpha)/2)*potential alpha c u (affine a b x)*a^((2+alpha)/2)) •
    ForcingDomain.localFactor alpha u (affine a b x)=
    a^(5/2:ℝ) • (potential alpha c u (affine a b x) • ForcingDomain.localFactor alpha u (affine a b x))
  rw [smul_smul]
  congr 1
  have hp : a^((3-alpha)/2)*a^((2+alpha)/2)=a^(5/2:ℝ) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  calc
    _ = (a^((3-alpha)/2)*a^((2+alpha)/2))*potential alpha c u (affine a b x) := by ring
    _ = _ := by rw [hp]

#print axioms potential_valuePullback
#print axioms localFactor_valuePullback
#print axioms forcing_valuePullback
end HartreeF.AffineForcing
