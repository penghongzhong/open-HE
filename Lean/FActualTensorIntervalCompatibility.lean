import FActualCompactHartreeTensorContract
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set Laplacian
open scoped Topology ContDiff SchwartzMap
namespace HartreeF.CompactPDEDualBridge
open EnergySpace ForcingDomain

/-- The unchanged real compact time test as a complex Schwartz function. -/
def complexTimeTest {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    SchwartzMap ℝ ℂ :=
  (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hη)

theorem complexTimeTest_apply {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (t : ℝ) : complexTimeTest hη hc t = (η t : ℂ) := rfl

theorem complexTimeTest_deriv {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (t : ℝ) :
    deriv (complexTimeTest hη hc) t = ((deriv η t : ℝ) : ℂ) :=
  ((hη.differentiable (by simp)).differentiableAt.hasDerivAt.ofReal_comp).deriv

theorem complexTimeTest_tsupport {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) : tsupport (complexTimeTest hη hc) = tsupport η := by
  change closure (Function.support (complexTimeTest hη hc)) = closure (Function.support η)
  congr 1
  ext t
  simp only [Function.mem_support, complexTimeTest_apply]
  norm_cast

/-- The exact historical zero-error compact tensor formula on a closed interval,
with the original u written explicitly and the literal Hartree spatial source.
It has no mass or bounded-dual derivative conclusion as an input. -/
def IntervalCompactHartreePDE (α c : ℝ) (u : ℝ → EnergyState) (a b : ℝ) : Prop :=
  ∀ η : SchwartzMap ℝ ℂ, tsupport η ⊆ Ioo a b →
    ∀ φ : Test, HasCompactSupport φ →
      (∫ t in Icc a b, -Complex.I * deriv η t * energyDistribution (u t) φ +
        η t * energyDistribution (u t) (Δ φ)) +
      (∫ t in Icc a b, η t * ∫ x : V, φ x * forcing α c (energyValue (u t)) x) = 0

/-- The actual tensor integrand vanishes outside the time-test support,
even if the ambient trajectory is arbitrary there. -/
theorem tensorOperator_eq_zero_of_notMem {α c : ℝ} (hH : OrdinaryHLS α c)
    (u : ℝ → EnergyState) {η : ℝ → ℝ} (φ : Test) {t : ℝ}
    (ht : t ∉ tsupport η) : tensorOperator hH u η φ t = 0 := by
  have h0 : η t = 0 := image_eq_zero_of_notMem_tsupport ht
  have hd : deriv η t = 0 := image_eq_zero_of_notMem_tsupport
    (fun ht' => ht (tsupport_deriv_subset ht'))
  simp only [tensorOperator, h0, hd, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]

/-- Restricting the whole-line test integral to any set containing the actual
support changes no value and needs no hypothesis outside that set. -/
theorem tensor_integral_eq_setIntegral {α c : ℝ} (hH : OrdinaryHLS α c)
    (u : ℝ → EnergyState) {η : ℝ → ℝ} (φ : Test) {A : Set ℝ}
    (hs : tsupport η ⊆ A) :
    (∫ t, tensorOperator hH u η φ t) = ∫ t in A, tensorOperator hH u η φ t := by
  symm
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => tensorOperator_eq_zero_of_notMem hH u φ (fun hx => ht (hs hx)))

/-- The literal historical interval tensor formula supplies the new open-domain
contract. This is an exact native formula bridge; the historical CriticalPath
package's original type still needs its separate trajectory identification. -/
theorem intervalPDE_to_openTensorPDE {α c a b : ℝ} (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} (hu : ContinuousOn u (Ioo a b))
    (hp : IntervalCompactHartreePDE α c u a b) :
    CompactHartreeTensorPDE hH u (Ioo a b) := by
  intro η hη hc hs φ hφ
  have hold := hp (complexTimeTest hη hc) ((complexTimeTest_tsupport hη hc).symm ▸ hs) φ hφ
  simp only [complexTimeTest_apply, complexTimeTest_deriv] at hold
  have hF : Continuous (fun v : EnergyState => ∫ x : V, φ x * forcing α c (energyValue v) x) := by
    convert (spatialTest_continuous hH φ).sub (stateTest_continuous (Δ φ)) using 1
    funext v
    change (∫ x : V, φ x * forcing α c (energyValue v) x) =
      spatialTest hH φ v - stateTest (Δ φ) v
    rw [spatialTest_literal_source]
    simp only [stateTest, add_sub_cancel_left]
  have h1 := BanachWeakDerivative.integrable_test_smul
    ((stateTest_continuous φ).comp_continuousOn hu)
    (hη.continuous_deriv (by simp)) hc.deriv (tsupport_deriv_subset.trans hs)
  have h2 := BanachWeakDerivative.integrable_test_smul
    ((stateTest_continuous (Δ φ)).comp_continuousOn hu) hη.continuous hc hs
  have h3 := BanachWeakDerivative.integrable_test_smul
    (hF.comp_continuousOn hu) hη.continuous hc hs
  have hiA : Integrable (fun t => -Complex.I * ((deriv η t : ℝ) : ℂ) *
      energyDistribution (u t) φ + (η t : ℂ) * energyDistribution (u t) (Δ φ)) := by
    convert (h1.const_mul (-Complex.I)).add h2 using 1
    ext t
    simp only [Complex.real_smul, stateTest, Function.comp_apply, Pi.add_apply, mul_assoc]
  have hiB : Integrable (fun t => (η t : ℂ) *
      ∫ x : V, φ x * forcing α c (energyValue (u t)) x) := by
    simpa only [Complex.real_smul, Function.comp_apply] using h3
  have he : tensorOperator hH u η φ = fun t =>
      (-Complex.I * ((deriv η t : ℝ) : ℂ) * energyDistribution (u t) φ +
        (η t : ℂ) * energyDistribution (u t) (Δ φ)) +
      (η t : ℂ) * ∫ x : V, φ x * forcing α c (energyValue (u t)) x := by
    funext t
    rw [tensorOperator, spatialTest_literal_source]
    simp only [stateTest, mul_add]
    ring
  rw [tensor_integral_eq_setIntegral hH u φ (hs.trans Ioo_subset_Icc_self), he,
    integral_add hiA.integrableOn hiB.integrableOn]
  exact hold

end HartreeF.CompactPDEDualBridge
