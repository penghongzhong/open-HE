import FLocalMildTrajectoryToDomainPDE
import Mathlib.MeasureTheory.Group.Integral

/-! Literal tensor-test equation i*sigma*d_s U + Delta U + F(U)=0
for U(s)=u(sigma*s). Reflection changes the time sign, without conjugating
or replacing the actual trajectory. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Set
open scoped Topology ContDiff
namespace HartreeF.Paper121SignedOrientation
open EnergySpace ForcingDomain CompactPDEDualBridge MaximalTrajectory
  SobolevStretch StationarySelfTest Retarded ActualStrichartz LinearWeakEquation

def SignedHartreeTensorPDE {alpha kernel : ℝ} (hH : OrdinaryHLS alpha kernel)
    (sigma : ℝ) (u : ℝ → EnergyState) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
    ∀ φ : Test, HasCompactSupport φ →
      (∫ t, -Complex.I * (sigma : ℂ) * ((deriv η t : ℝ) : ℂ) * stateTest φ (u t) +
        (η t : ℂ) * spatialTest hH φ (u t)) = 0

theorem signed_tensor_of_global_tensor {alpha kernel : ℝ}
    (hH : OrdinaryHLS alpha kernel) (u : ℝ → EnergyState)
    (hp : CompactHartreeTensorPDE hH u univ)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    SignedHartreeTensorPDE hH sigma (fun t => u (sigma*t)) := by
  rcases hsigma with rfl | rfl
  · intro η hη hc φ hφ
    simpa only [one_mul, Complex.ofReal_one, mul_one, tensorOperator] using
      hp η hη hc (subset_univ _) φ hφ
  · intro η hη hc φ hφ
    let ηr : ℝ → ℝ := fun t => η (-t)
    have hr : ContDiff ℝ ∞ ηr := hη.comp contDiff_id.neg
    have hrc : HasCompactSupport ηr := hc.comp_homeomorph (Homeomorph.neg ℝ)
    have hd (t : ℝ) : deriv ηr t = -(deriv η (-t)) := by
      have hh : HasDerivAt η (deriv η (-t)) (-t) :=
        (hη.differentiable (by simp) (-t)).hasDerivAt
      simpa only [mul_neg_one] using (hh.comp t (hasDerivAt_neg t)).deriv
    have he (t : ℝ) :
        -Complex.I * ((-1 : ℝ) : ℂ) * ((deriv η t : ℝ) : ℂ) * stateTest φ (u ((-1)*t)) +
          (η t : ℂ) * spatialTest hH φ (u ((-1)*t)) =
          tensorOperator hH u ηr φ (-t) := by
      simp only [tensorOperator, hd, ηr, neg_neg, neg_one_mul,
        Complex.ofReal_neg, Complex.ofReal_one]
      ring
    calc
      _ = ∫ t, tensorOperator hH u ηr φ (-t) :=
        integral_congr_ae (Filter.Eventually.of_forall he)
      _ = ∫ t, tensorOperator hH u ηr φ t := integral_neg_eq_self _ volume
      _ = 0 := hp ηr hr hrc (subset_univ _) φ hφ

theorem actual_global_signed_tensor
    (hDensity : OrdinaryH1Density) {K alpha kernel s C0 Ch Cr : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha kernel)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    {f : EnergyState} (U : LocalMildTrajectory alpha kernel s f)
    (hglobal : U.domain = univ) (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1) :
    SignedHartreeTensorPDE hH sigma (fun t => U.state (sigma*t)) := by
  have hp := HartreeMildPDEProducer.localMildTrajectory_domain_tensorPDE
    hDensity hSob hH h0 hfree hret hgen U
  rw [hglobal] at hp
  exact signed_tensor_of_global_tensor hH U.state hp sigma hsigma

end HartreeF.Paper121SignedOrientation
