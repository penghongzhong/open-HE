import FBanachWeakTimeRegularity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped Topology ContDiff
namespace HartreeF.DenseDualTime

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Tested actual Bochner integrals on a dense set identify the continuous dual itself. -/
theorem integral_eq_of_dense_tests {d : X → E} (hd : DenseRange d)
    {f g : ℝ → (E →L[ℝ] ℝ)} (hf : Integrable f) (hg : Integrable g)
    (h : ∀ x, (∫ t, f t (d x)) = -(∫ t, g t (d x))) :
    (∫ t, f t) = -(∫ t, g t) := by
  have he : (fun v => (∫ t, f t) v) = (fun v => (-(∫ t, g t)) v) := by
    apply hd.equalizer (∫ t, f t).continuous (-(∫ t, g t)).continuous
    funext x
    change (∫ t, f t) (d x) = (-(∫ t, g t)) (d x)
    simpa only [neg_apply, ContinuousLinearMap.integral_apply hf,
      ContinuousLinearMap.integral_apply hg] using h x
  exact ContinuousLinearMap.ext (congrFun he)

/-- Scalar weak identities against a dense set of spatial vectors lift to the
actual norm-dual valued distribution identity. No time derivative is an input. -/
theorem weak_identity_of_dense_tests {d : X → E} (hd : DenseRange d)
    {S : Set ℝ} {f g : ℝ → (E →L[ℝ] ℝ)}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (h : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ S →
      ∀ x, (∫ t, deriv η t * f t (d x)) = -(∫ t, η t * g t (d x))) :
    ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ S →
      (∫ t, deriv η t • f t) = -(∫ t, η t • g t) := by
  intro η hη hc hs
  apply integral_eq_of_dense_tests hd
    (BanachWeakDerivative.integrable_test_smul hf (hη.continuous_deriv (by simp))
      hc.deriv (tsupport_deriv_subset.trans hs))
    (BanachWeakDerivative.integrable_test_smul hg hη.continuous hc hs)
  intro x
  simpa only [smul_apply, smul_eq_mul] using h η hη hc hs x

/-- Full generic weak-to-classical lift from dense spatial tests on the exact open domain. -/
theorem hasDerivAt_of_dense_weak_tests {d : X → E} (hd : DenseRange d)
    {S : Set ℝ} (hS : IsOpen S) {f g : ℝ → (E →L[ℝ] ℝ)}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (h : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ S →
      ∀ x, (∫ t, deriv η t * f t (d x)) = -(∫ t, η t * g t (d x)))
    {t : ℝ} (ht : t ∈ S) : HasDerivAt f (g t) t :=
  BanachWeakDerivative.hasDerivAt_of_weak_time_derivative hS hf hg
    (weak_identity_of_dense_tests hd hf hg h) ht

end HartreeF.DenseDualTime
