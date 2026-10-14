import WeakDirectionalStretch
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
A native classical-to-weak gradient producer on the actual F Euclidean space.
All three product-integrability hypotheses of the ordinary integration-by-parts
lemma are produced from continuous fields and an actual compact smooth test.
No weak-gradient transformation or integration-by-parts identity is an input.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace HartreeF.SobolevStretch

/-- Actual differentiability and the actual continuous gradient pairing imply
the genuine C-infinity compact-test weak-gradient identity. -/
theorem hasWeakGradient_of_differentiable {u : Space → ℝ} {V : Space → Space}
    (hu : Differentiable ℝ u) (hV : Continuous V)
    (hgrad : ∀ x v, fderiv ℝ u x v = ⟪V x,v⟫) :
    HasWeakGradient u V := by
  have hul : LocallyIntegrable u volume := hu.continuous.locallyIntegrable
  have hVl : LocallyIntegrable V volume := hV.locallyIntegrable
  refine ⟨hul,hVl,?_⟩
  intro v φ hφ hc
  have ht := weak_test_integrable hul hVl hφ hc v
  have hfg : Integrable (fun x => u x * φ x) volume := by
    simpa only [smul_eq_mul] using
      hul.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hfg' : Integrable (fun x => fderiv ℝ u x v * φ x) volume := by
    simpa only [hgrad] using ht.2
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hfg' ht.1 hfg
    (fun x _ => hu x) (fun x _ => hφ.differentiable (by simp) x)
  simpa only [hgrad] using h

theorem hasWeakGradient_zero : HasWeakGradient (fun _ : Space => (0:ℝ)) (fun _ => 0) := by
  apply hasWeakGradient_of_differentiable (differentiable_const (0:ℝ)) continuous_const
  intro x v
  simp

#print axioms hasWeakGradient_of_differentiable
#print axioms hasWeakGradient_zero
end HartreeF.SobolevStretch
