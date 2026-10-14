import FAffineSchwartzFree
import FRetardedScalarL2

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped SchwartzMap ENNReal
namespace HartreeF.AffinePath
open EnergySpace CriticalAffine FreeAffine FreeFlow Retarded

/-- The actual bilinear transpose of the homogeneous spatial action. -/
def dualAffineTest {a : ℝ} (ha : 0<a) (b : Space) : FreeFlow.Test →L[ℂ] FreeFlow.Test :=
  (Real.sqrt a*(a^3)⁻¹) • SchwartzMap.compCLMOfAntilipschitz ℂ
    (show (affine a⁻¹ (-(a⁻¹ • b))).HasTemperateGrowth by unfold affine; fun_prop)
    (affine_antilipschitz (inv_pos.mpr ha) (-(a⁻¹ • b)))

theorem dualAffineTest_apply {a : ℝ} (ha : 0<a) (b : Space) (φ : FreeFlow.Test) (x : Space) :
    dualAffineTest ha b φ x=(Real.sqrt a*(a^3)⁻¹) • φ (affine a⁻¹ (-(a⁻¹ • b)) x) := rfl

theorem dualAffineTest_amplitude {a : ℝ} (ha : 0<a) (b : Space) (φ : FreeFlow.Test) (x : Space) :
    dualAffineTest ha b φ x=a^(-5/2:ℝ) • φ (a⁻¹ • (x-b)) := by
  have hi : (a^3)⁻¹=a^(-3:ℝ) := by rw [Real.rpow_neg ha.le]; simp
  have hk : Real.sqrt a*(a^3)⁻¹=a^(-5/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,hi,← Real.rpow_add ha]
    norm_num
  rw [dualAffineTest_apply,hk]
  congr 2
  simp only [affine,sub_eq_add_neg,smul_add,smul_neg]

/-- Literal pairing transport, valid before any Lp completion is chosen. -/
theorem valuePullback_pairing {a : ℝ} (ha : 0<a) (b : Space)
    (f : Space → ℂ) (φ : FreeFlow.Test) :
    (∫ x, φ x*valuePullback a b f x)=∫ y, dualAffineTest ha b φ y*f y := by
  have hinv (x : Space) : affine a⁻¹ (-(a⁻¹ • b)) (affine a b x)=x := by
    simp [affine,smul_add,smul_smul,ha.ne']
  have hj := affine_integral ha b (fun y => φ (affine a⁻¹ (-(a⁻¹ • b)) y)*f y)
  simp only [hinv] at hj
  calc
    _ = Real.sqrt a • ∫ x, φ x*f (affine a b x) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [valuePullback,Complex.real_smul]
      ring
    _ = Real.sqrt a • ((a^3)⁻¹ • ∫ y, φ (affine a⁻¹ (-(a⁻¹ • b)) y)*f y) := congrArg _ hj
    _ = (Real.sqrt a*(a^3)⁻¹) • ∫ y, φ (affine a⁻¹ (-(a⁻¹ • b)) y)*f y := by rw [smul_smul]
    _ = _ := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [dualAffineTest_apply]
      simp only [Complex.real_smul]
      ring

/-- Bilinear, not Hermitian: no conjugation and no sign change is inserted. -/
def testPair (φ ψ : FreeFlow.Test) : ℂ := ∫ x, φ x*ψ x

theorem testPair_comm (φ ψ : FreeFlow.Test) : testPair φ ψ=testPair ψ φ := by
  unfold testPair
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _

theorem affineSchwartz_bilinear_transpose {a : ℝ} (ha : 0<a) (b : Space) (φ ψ : FreeFlow.Test) :
    testPair φ (affineSchwartz ha b ψ)=testPair (dualAffineTest ha b φ) ψ := by
  exact valuePullback_pairing ha b ψ φ

/-- The exact existing Fourier transpose relation, proved through the actual
Schwartz-to-distribution identity. -/
theorem freeSchwartz_bilinear_transpose (t : ℝ) (φ ψ : FreeFlow.Test) :
    testPair φ (freeSchwartz t ψ)=testPair (freeTest t φ) ψ := by
  have h := congrArg (fun T : FreeFlow.TD => T φ) (freeSchwartz_energyDistribution t ψ)
  simpa only [testPair,schwartzEnergyState_distribution,free_apply,
    SchwartzMap.toTemperedDistributionCLM_apply_apply,smul_eq_mul] using h

/-- Native covariance of the bilinear free test operator. It is not an
identification of freeTest with freeSchwartz by name or definition. -/
theorem dualAffineTest_freeTest {a : ℝ} (ha : 0<a) (b : Space) (t : ℝ) (φ : FreeFlow.Test) :
    dualAffineTest ha b (freeTest t φ)=freeTest (a^2*t) (dualAffineTest ha b φ) := by
  apply SchwartzMap.injective_toLp 2 volume
  apply l2_distribution_injective
  ext ψ
  simp only [Lp.toTemperedDistribution_toLp_eq,
    SchwartzMap.toTemperedDistributionCLM_apply_apply,smul_eq_mul]
  change testPair ψ (dualAffineTest ha b (freeTest t φ))=
    testPair ψ (freeTest (a^2*t) (dualAffineTest ha b φ))
  calc
    _ = testPair (dualAffineTest ha b (freeTest t φ)) ψ := testPair_comm _ _
    _ = testPair (freeTest t φ) (affineSchwartz ha b ψ) :=
      (affineSchwartz_bilinear_transpose ha b _ _).symm
    _ = testPair φ (freeSchwartz t (affineSchwartz ha b ψ)) :=
      (freeSchwartz_bilinear_transpose t _ _).symm
    _ = testPair φ (affineSchwartz ha b (freeSchwartz (a^2*t) ψ)) := by rw [freeSchwartz_affine]
    _ = testPair (dualAffineTest ha b φ) (freeSchwartz (a^2*t) ψ) :=
      affineSchwartz_bilinear_transpose ha b _ _
    _ = testPair (freeTest (a^2*t) (dualAffineTest ha b φ)) ψ :=
      freeSchwartz_bilinear_transpose (a^2*t) _ _
    _ = _ := testPair_comm _ _

#print axioms dualAffineTest
#print axioms dualAffineTest_apply
#print axioms dualAffineTest_amplitude
#print axioms valuePullback_pairing
#print axioms testPair
#print axioms testPair_comm
#print axioms affineSchwartz_bilinear_transpose
#print axioms freeSchwartz_bilinear_transpose
#print axioms dualAffineTest_freeTest
end HartreeF.AffinePath
