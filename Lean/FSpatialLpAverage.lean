import FProfileMixedTails
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Translation in the actual finite-exponent spatial Lp quotient. -/
def lpShift (y : Space) (f : Lp E p (volume : Measure Space)) : Lp E p (volume : Measure Space) :=
  Lp.compMeasurePreserving (fun x => x + y) (measurePreserving_add_right volume y) f

theorem lpShift_norm (y : Space) (f : Lp E p (volume : Measure Space)) :
    ‖lpShift y f‖ = ‖f‖ := Lp.norm_compMeasurePreserving f _

theorem lpShift_zero (f : Lp E p (volume : Measure Space)) : lpShift 0 f = f := by
  unfold lpShift
  simp only [add_zero]
  exact Lp.compMeasurePreserving_id_apply f

theorem lpShift_coe_ae (y : Space) (f : Lp E p (volume : Measure Space)) :
    (lpShift y f : Space → E) =ᵐ[volume] (fun x => f (x + y)) :=
  Lp.coeFn_compMeasurePreserving f _

variable [Fact (1 ≤ p)]

/-- Strong translation continuity, proved using the existing native measure-preserving API. -/
theorem lpShift_continuous (hp : p ≠ ∞) (f : Lp E p (volume : Measure Space)) :
    Continuous (fun y : Space => lpShift y f) := by
  let g : Space → C(Space, Space) := fun y => ⟨fun x => x + y, continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun y => measurePreserving_add_right volume y) hp

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- A spatial mollifier is first realized as a Bochner average of actual Lp translations.
Identification with the pointwise convolution is a separate theorem, not assumed here. -/
def lpMollify (φ : ContDiffBump (0 : Space))
    (f : Lp E p (volume : Measure Space)) : Lp E p (volume : Measure Space) :=
  ((φ.normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (fun y => lpShift y f)) 0

omit [CompleteSpace E] in
theorem lpMollify_integral (φ : ContDiffBump (0 : Space))
    (f : Lp E p (volume : Measure Space)) :
    lpMollify φ f = ∫ y : Space, φ.normed volume y • lpShift (-y) f := by
  simp only [lpMollify, convolution, ContinuousLinearMap.lsmul_apply, zero_sub]

omit [CompleteSpace E] in
/-- Each nonnegative normalized spatial average contracts the actual Lp norm. -/
theorem lpMollify_norm_le (φ : ContDiffBump (0 : Space))
    (f : Lp E p (volume : Measure Space)) : ‖lpMollify φ f‖ ≤ ‖f‖ := by
  rw [lpMollify_integral]
  have hb : ∀ y : Space, ‖φ.normed volume y • lpShift (-y) f‖ ≤ φ.normed volume y * ‖f‖ := by
    intro y
    rw [norm_smul, lpShift_norm, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed y)]
  have hi := φ.integrable_normed (μ := (volume : Measure Space)) |>.mul_const ‖f‖
  calc
    ‖∫ y : Space, φ.normed volume y • lpShift (-y) f‖ ≤ ∫ y : Space, φ.normed volume y * ‖f‖ :=
      norm_integral_le_of_norm_le hi (ae_of_all _ hb)
    _ = ‖f‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- The Bochner spatial approximate identity converges in every finite Lp exponent. -/
theorem lpMollify_tendsto {ι : Type*} {l : Filter ι} (hp : p ≠ ∞)
    {φ : ι → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun n => (φ n).rOut) l (𝓝 0))
    (f : Lp E p (volume : Measure Space)) :
    Tendsto (fun n => lpMollify (φ n) f) l (𝓝 f) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure Space)) hφ (lpShift_continuous hp f) 0
  simpa only [lpMollify, lpShift_zero] using h

#print axioms lpShift_continuous
#print axioms lpMollify_norm_le
#print axioms lpMollify_tendsto
end HartreeF.ProfileSpatialSmoothing
