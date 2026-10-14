import DirectionalCriticalDifference
import HartreeForcingDirectionalIdentity

/-! Independent consumer: the literal six-majorant candidate is the actual
weak directional forcing derivative, and its critical estimate transfers to it. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace
namespace HartreeF.DerivativeMajorizationReview
open ForcingDomain GradientMajorants WeakHartreeChain WeakHartreeProduct DerivativeMajorization
open SobolevStretch StationarySelfTest

def actualDirectionalDerivative (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) (e : Space) : Space → ℂ :=
  directionalField (forcingGradientRe α c u U V) (forcingGradientIm α c u U V) e

theorem actual_directional_candidate_ae {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) (e : Space) :
    actualDirectionalDerivative α c u U V e =ᵐ[volume]
      directionalCandidate α c u (directionalField U V e) :=
  forcingGradient_directional_ae hH hu6 hu10 hU hV e

theorem zero_direction_candidate (α c : ℝ) (u : Space → ℂ) :
    directionalCandidate α c u (fun _ => 0) = 0 := by
  funext x
  simp [directionalCandidate,directionalDensity,rieszConvolution]

theorem candidate_actual_real_weak_test (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume)
    (e : Space) {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => (directionalCandidate α c u (directionalField U V e) x).re*φ x) volume ∧
    (∫ x, (forcing α c u x).re*fderiv ℝ φ x e) =
      -(∫ x, (directionalCandidate α c u (directionalField U V e) x).re*φ x) := by
  have hw := (hartree_forcing_weak_gradients hDensity hSob hH hu hu10 hU hV).1
  have he := actual_directional_candidate_ae hH hu.function_L6 hu10 hU hV e
  have hp : (fun x => ⟪forcingGradientRe α c u U V x,e⟫*φ x) =ᵐ[volume]
      (fun x => (directionalCandidate α c u (directionalField U V e) x).re*φ x) := by
    filter_upwards [he] with x hx
    have hr := congrArg Complex.re hx
    change ⟪forcingGradientRe α c u U V x,e⟫ = _ at hr
    rw [hr]
  refine ⟨(hw.test_integrable hφ hc e).2.congr hp,?_⟩
  rw [hw.integration_by_parts e φ hφ hc,integral_congr_ae hp]

theorem actual_directional_critical_difference {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (u v : Space → ℂ) (U V P Q : Space → Space),
      InDotH1 u U V → InDotH1 v P Q → MemLp u 10 volume → MemLp v 10 volume →
      MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume → MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume →
      MemLp P (ENNReal.ofReal (30/13 : ℝ)) volume → MemLp Q (ENNReal.ofReal (30/13 : ℝ)) volume →
      ∀ e : Space,
      MemLp (actualDirectionalDerivative α c u U V e-actualDirectionalDerivative α c v P Q e)
        (ENNReal.ofReal (6/5 : ℝ)) volume ∧
      (eLpNorm (actualDirectionalDerivative α c u U V e-actualDirectionalDerivative α c v P Q e)
        (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤
        (C : ℝ)*(singleWeight α (sumAmplitude u v) (fun x => ‖directionalField U V e x-directionalField P Q e x‖)+
          spacetimeDifferenceWeight α (sumAmplitude u v) (differenceAmplitude u v) (fun x => ‖directionalField P Q e x‖)+
          mixedDifferenceWeight α (sumAmplitude u v) (differenceAmplitude u v) (fun x => ‖directionalField P Q e x‖)) := by
  obtain ⟨C,hC⟩ := directional_candidate_critical_difference hH
  refine ⟨C,?_⟩
  intro u v U V P Q hu hv hu10 hv10 hU hV hP hQ e
  have hc := hC u v (directionalField U V e) (directionalField P Q e)
    hu.function_L6 hv.function_L6 hu10 hv10 (directionalField_memLp hU hV e) (directionalField_memLp hP hQ e)
  have he := (actual_directional_candidate_ae hH hu.function_L6 hu10 hU hV e).sub
    (actual_directional_candidate_ae hH hv.function_L6 hv10 hP hQ e)
  refine ⟨MemLp.ae_eq he.symm hc.1,?_⟩
  rw [eLpNorm_congr_ae he]
  exact hc.2

#print axioms actualDirectionalDerivative
#print axioms actual_directional_candidate_ae
#print axioms zero_direction_candidate
#print axioms candidate_actual_real_weak_test
#print axioms actual_directional_critical_difference
end HartreeF.DerivativeMajorizationReview
