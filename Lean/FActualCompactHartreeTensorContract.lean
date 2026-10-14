import FActualDualDiagonalFlux
import FPhysicalChargeDualIdentification
import FBanachWeakDerivativeHelpers

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set Laplacian
open scoped Topology ENNReal ContDiff SchwartzMap
namespace HartreeF.CompactPDEDualBridge
open EnergySpace LocalChargeBridge LocalDualSource ForcingDomain ForcingContinuity
attribute [local instance] energyRealSpace energyDualComplexNorm energyDualRealNorm
  energyDualComplexSpace energyDualRealSpace
local instance : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩

/-- The original state distribution evaluated on the actual spatial test. -/
def stateTest (φ : Test) (u : EnergyState) : ℂ := energyDistribution u φ

/-- The original Laplacian distribution plus the literal Hartree forcing distribution. -/
def spatialTest {α c : ℝ} (hH : OrdinaryHLS α c) (φ : Test) (u : EnergyState) : ℂ :=
  energyDistribution u (Δ φ) + Lp.toTemperedDistribution (forcingLp hH (energyValue u)) φ

theorem stateTest_continuous (φ : Test) : Continuous (stateTest φ) :=
  (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).continuous.comp energyDistribution.continuous

theorem spatialTest_continuous {α c : ℝ} (hH : OrdinaryHLS α c) (φ : Test) :
    Continuous (spatialTest hH φ) :=
  (stateTest_continuous (Δ φ)).add
    ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).continuous.comp
      ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) (ENNReal.ofReal (6/5 : ℝ))).continuous.comp
        ((forcingLp_continuous hH).comp energyValue.continuous)))

/-- No alternate source is supplied: the source term is the actual spatial Hartree integral. -/
theorem spatialTest_literal_source {α c : ℝ} (hH : OrdinaryHLS α c) (φ : Test) (u : EnergyState) :
    spatialTest hH φ u = energyDistribution u (Δ φ) +
      ∫ x : V, φ x * forcing α c (energyValue u) x := by
  unfold spatialTest
  congr 1
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(forcing_memLp hH (Lp.memLp (energyValue u))).coeFn_toLp] with x hx
  change φ x * forcingLp hH (energyValue u) x = _
  rw [show forcingLp hH (energyValue u) x = _ from hx]

/-- Actual tensor-test operator for i*u_t + Delta*u + F(u)=0.
Time tests are real scalar smooth compact functions; spatial tests are complex. -/
def tensorOperator {α c : ℝ} (hH : OrdinaryHLS α c) (u : ℝ → EnergyState)
    (η : ℝ → ℝ) (φ : Test) (t : ℝ) : ℂ :=
  -Complex.I * ((deriv η t : ℝ) : ℂ) * stateTest φ (u t) +
    (η t : ℂ) * spatialTest hH φ (u t)

/-- Genuine compact tensor distribution PDE on exactly S, without a time derivative,
localized charge, dual derivative, flux, mild formula or L2 premise. -/
def CompactHartreeTensorPDE {α c : ℝ} (hH : OrdinaryHLS α c)
    (u : ℝ → EnergyState) (S : Set ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ S →
    ∀ φ : Test, HasCompactSupport φ → ∫ t, tensorOperator hH u η φ t = 0

/-- The tensor integrals are genuine Bochner integrals from actual state/source continuity,
with no conditions on u outside S. -/
theorem tensorOperator_integrable {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hu : ContinuousOn u S)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ S) (φ : Test) : Integrable (tensorOperator hH u η φ) := by
  have hiB := BanachWeakDerivative.integrable_test_smul
    ((stateTest_continuous φ).comp_continuousOn hu)
    (hη.continuous_deriv (by simp)) hc.deriv (tsupport_deriv_subset.trans hs)
  have hiW := BanachWeakDerivative.integrable_test_smul
    ((spatialTest_continuous hH φ).comp_continuousOn hu) hη.continuous hc hs
  convert (hiB.const_mul (-Complex.I)).add hiW using 1
  ext t
  simp only [tensorOperator, Complex.real_smul, mul_assoc, Function.comp_apply, Pi.add_apply]

/-- Exact split of the actual weak equation, after the required integrability has been proved. -/
theorem tensor_integral_split {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hu : ContinuousOn u S)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ S) (φ : Test) :
    (∫ t, tensorOperator hH u η φ t) =
      -Complex.I * (∫ t, deriv η t • stateTest φ (u t)) +
        ∫ t, η t • spatialTest hH φ (u t) := by
  have hiB := BanachWeakDerivative.integrable_test_smul
    ((stateTest_continuous φ).comp_continuousOn hu)
    (hη.continuous_deriv (by simp)) hc.deriv (tsupport_deriv_subset.trans hs)
  have hiW := BanachWeakDerivative.integrable_test_smul
    ((spatialTest_continuous hH φ).comp_continuousOn hu) hη.continuous hc hs
  have he : tensorOperator hH u η φ =
      fun t => -Complex.I * (deriv η t • stateTest φ (u t)) + η t • spatialTest hH φ (u t) := by
    funext t
    simp only [tensorOperator, Complex.real_smul, mul_assoc]
  rw [he]
  change (∫ t, -Complex.I * (deriv η t • stateTest φ (u t)) + η t • spatialTest hH φ (u t)) = _
  simp only [Function.comp_apply] at hiB hiW
  calc
    _ = (∫ t, -Complex.I * (deriv η t • stateTest φ (u t))) +
        ∫ t, η t • spatialTest hH φ (u t) := integral_add (hiB.const_mul (-Complex.I)) hiW
    _ = _ := by rw [integral_const_mul]

end HartreeF.CompactPDEDualBridge
