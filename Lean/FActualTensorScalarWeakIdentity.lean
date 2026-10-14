import FActualCompactHartreeTensorContract

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
open MeasureTheory Set
open scoped Topology ContDiff
namespace HartreeF.CompactPDEDualBridge
open EnergySpace ForcingDomain

/-- From the actual tensor PDE to its real weak-time identity, with the
Schroedinger factor i and both actual integrals preserved. -/
theorem real_weak_identity_of_tensor {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ S) (φ : Test) (hφ : HasCompactSupport φ) :
    (∫ t, deriv η t * (stateTest φ (u t)).re) =
      -(∫ t, η t * (Complex.I * spatialTest hH φ (u t)).re) := by
  have hiB := BanachWeakDerivative.integrable_test_smul
    ((stateTest_continuous φ).comp_continuousOn hu)
    (hη.continuous_deriv (by simp)) hc.deriv (tsupport_deriv_subset.trans hs)
  have hiW := BanachWeakDerivative.integrable_test_smul
    ((spatialTest_continuous hH φ).comp_continuousOn hu) hη.continuous hc hs
  simp only [Function.comp_apply] at hiB hiW
  have hz := hp η hη hc hs φ hφ
  rw [tensor_integral_split hH hu hη hc hs φ] at hz
  let A : ℂ := ∫ t, deriv η t • stateTest φ (u t)
  let B : ℂ := ∫ t, η t • spatialTest hH φ (u t)
  have he : A = -(Complex.I * B) := by
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      A + Complex.I * B = Complex.I * (-Complex.I * A + B) := by
        simp only [mul_add, mul_neg, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_neg]
      _ = 0 := by rw [show -Complex.I * A + B = 0 from hz, mul_zero]
  have hRe := congrArg Complex.re he
  have hleft : A.re = ∫ t, deriv η t * (stateTest φ (u t)).re := by
    change Complex.reCLM (∫ t, deriv η t • stateTest φ (u t)) = _
    rw [← Complex.reCLM.integral_comp_comm hiB]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [Complex.reCLM_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hright : (Complex.I * B).re = ∫ t, η t * (Complex.I * spatialTest hH φ (u t)).re := by
    change Complex.reCLM (Complex.I * ∫ t, η t • spatialTest hH φ (u t)) = _
    rw [← integral_const_mul, ← Complex.reCLM.integral_comp_comm (hiW.const_mul Complex.I)]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [Complex.reCLM_apply, Complex.real_smul]
    rw [show Complex.I * ((η t : ℂ) * spatialTest hH φ (u t)) =
      (η t : ℂ) * (Complex.I * spatialTest hH φ (u t)) by ring]
    simp
  simpa only [Complex.neg_re, hleft, hright] using hRe

end HartreeF.CompactPDEDualBridge
