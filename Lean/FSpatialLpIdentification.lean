import FSpatialLpAverage
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Integration over a finite measurable set is a continuous functional on spatial Lp. -/
def setIntegralLp (s : Set Space) (hs : MeasurableSet s) (hμs : volume s ≠ ∞) :
    Lp E p (volume : Measure Space) →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ).lpPairing volume q p
    (indicatorConstLp q hs hμs (1 : ℝ))

theorem setIntegralLp_apply (s : Set Space) (hs : MeasurableSet s) (hμs : volume s ≠ ∞)
    (f : Lp E p (volume : Measure Space)) :
    setIntegralLp (q := q) s hs hμs f = ∫ x in s, f x := by
  rw [setIntegralLp, ContinuousLinearMap.lpPairing_eq_integral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
  rw [ContinuousLinearMap.lsmul_apply, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

omit [Fact (1 ≤ q)] [q.HolderConjugate p] [CompleteSpace E] in
theorem lpMollify_integrable_orbit (hp : p ≠ ∞) (φ : ContDiffBump (0 : Space))
    (f : Lp E p (volume : Measure Space)) :
    Integrable (fun y : Space => φ.normed volume y • lpShift (-y) f) volume := by
  exact (φ.continuous_normed.smul ((lpShift_continuous hp f).comp continuous_neg)).integrable_of_hasCompactSupport
    φ.hasCompactSupport_normed.smul_right

include q in
/-- For Lp functions that are also integrable, the quotient average is the literal convolution.
The integrability hypothesis is available after the previously constructed compact spatial cutoff. -/
theorem lpMollify_coe_ae_of_integrable (hp : p ≠ ∞) (φ : ContDiffBump (0 : Space))
    (f : Lp E p (volume : Measure Space)) (hf : Integrable f volume) :
    (lpMollify φ f : Space → E) =ᵐ[volume]
      ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : Space → E)) := by
  let B : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hprod := (φ.integrable_normed (μ := (volume : Measure Space))).convolution_integrand B hf
  have hconv := (φ.integrable_normed (μ := (volume : Measure Space))).integrable_convolution B hf
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact integrableOn_Lp_of_measure_ne_top _ Fact.out hμs.ne
  · intro s _ _
    exact hconv.integrableOn
  · intro s hs hμs
    let T := setIntegralLp (p := p) (q := q) (E := E) s hs hμs.ne
    calc
      (∫ x in s, (lpMollify φ f : Space → E) x) = T (lpMollify φ f) :=
        (setIntegralLp_apply s hs hμs.ne _).symm
      _ = ∫ y : Space, T (φ.normed volume y • lpShift (-y) f) := by
        rw [lpMollify_integral, ← T.integral_comp_comm (lpMollify_integrable_orbit hp φ f)]
      _ = ∫ y : Space, ∫ x in s, φ.normed volume y • f (x - y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [map_smul, setIntegralLp_apply, ← integral_smul]
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (lpShift_coe_ae (-y) f)] with x hx
        simp only [hx, sub_eq_add_neg]
      _ = ∫ x in s, ∫ y : Space, φ.normed volume y • f (x - y) := by
        have hr : Integrable (fun z : Space × Space => φ.normed volume z.2 • f (z.1 - z.2))
            ((volume.restrict s).prod volume) := by
          rw [Measure.restrict_prod_eq_prod_univ]
          exact hprod.restrict
        exact (integral_integral_swap hr).symm
      _ = ∫ x in s, ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : Space → E)) x := rfl

#print axioms lpMollify_coe_ae_of_integrable
end HartreeF.ProfileSpatialSmoothing
