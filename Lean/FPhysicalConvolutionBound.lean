import FYoungKernelScaling
import Mathlib.Analysis.Convolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap Convolution
namespace HartreeF.PhysicalLowpass
open EnergySpace YoungSource

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A literal everywhere-defined spatial integral, not a selected point value of an Lp class. -/
def convolutionValue (k : Test) (f : Lp ℂ p (volume : Measure V)) (x : V) : ℂ :=
  ∫ y : V, f y * k (x - y)

omit [Fact (1 ≤ p)] in
theorem convolutionValue_measurable (k : Test) (f : Lp ℂ p (volume : Measure V)) :
    AEStronglyMeasurable (convolutionValue k f) volume :=
  (Lp.aestronglyMeasurable f).convolution (L := ContinuousLinearMap.mul ℂ ℂ)
    k.continuous.aestronglyMeasurable

variable {r : ℝ≥0∞} [Fact (1 ≤ r)] [p.HolderConjugate r]

include r in
omit [Fact (1 ≤ p)] [Fact (1 ≤ r)] in
theorem convolutionValue_integrable (k : Test) (f : Lp ℂ p (volume : Measure V)) (x : V) :
    Integrable (fun y : V => f y * k (x - y)) volume :=
  ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ)
    (Lp.memLp f) (k.memLp r volume) x

theorem convolutionValue_norm (k : Test) (f : Lp ℂ p (volume : Measure V)) (x : V) :
    ‖convolutionValue k f x‖ ≤ ‖k.toLp r volume‖ * ‖f‖ := by
  have he := enorm_convolution_le (L := ContinuousLinearMap.mul ℂ ℂ)
    (p := p) (q := r) (Lp.aestronglyMeasurable f) k.continuous.aestronglyMeasurable x
  have ht : ‖ContinuousLinearMap.mul ℂ ℂ‖ₑ * eLpNorm (f : V → ℂ) p volume *
      eLpNorm (k : V → ℂ) r volume ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top enorm_ne_top (Lp.memLp f).eLpNorm_ne_top)
      (k.memLp r volume).eLpNorm_ne_top
  have hr := ENNReal.toReal_mono ht he
  simp only [ENNReal.toReal_mul, toReal_enorm, ← Lp.norm_def, ← SchwartzMap.norm_toLp] at hr
  calc
    _ ≤ ‖ContinuousLinearMap.mul ℂ ℂ‖ * ‖f‖ * ‖k.toLp r volume‖ := hr
    _ ≤ 1 * ‖f‖ * ‖k.toLp r volume‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℂ ℂ
    _ = _ := by ring

include r in
theorem convolutionValue_memLp_top (k : Test) (f : Lp ℂ p (volume : Measure V)) :
    MemLp (convolutionValue k f) ∞ volume :=
  memLp_top_of_bound (convolutionValue_measurable k f) (‖k.toLp r volume‖ * ‖f‖)
    (Eventually.of_forall (convolutionValue_norm (r := r) k f))

/-- Actual L-infinity class of the literal pointwise convolution. -/
def convolutionInfinity (k : Test) (f : Lp ℂ p (volume : Measure V)) :
    Lp ℂ ∞ (volume : Measure V) :=
  (convolutionValue_memLp_top (r := r) k f).toLp (convolutionValue k f)

theorem convolutionInfinity_coe (k : Test) (f : Lp ℂ p (volume : Measure V)) :
    (convolutionInfinity (r := r) k f : V → ℂ) =ᵐ[volume] convolutionValue k f :=
  (convolutionValue_memLp_top (r := r) k f).coeFn_toLp

theorem convolutionInfinity_norm (k : Test) (f : Lp ℂ p (volume : Measure V)) :
    ‖convolutionInfinity (r := r) k f‖ ≤ ‖k.toLp r volume‖ * ‖f‖ := by
  rw [convolutionInfinity, Lp.norm_toLp,
    eLpNorm_exponent_top (convolutionValue_measurable k f)]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  exact eLpNormEssSup_le_of_ae_bound
    (Eventually.of_forall (convolutionValue_norm (r := r) k f))

include r in
omit [Fact (1 ≤ p)] [Fact (1 ≤ r)] in
theorem convolutionValue_add (k : Test) (f g : Lp ℂ p (volume : Measure V)) (x : V) :
    convolutionValue k (f + g) x = convolutionValue k f x + convolutionValue k g x := by
  rw [convolutionValue, convolutionValue, convolutionValue,
    ← integral_add (convolutionValue_integrable (r := r) k f x)
      (convolutionValue_integrable (r := r) k g x)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with y hy
  simp only [hy, Pi.add_apply, add_mul]

omit [Fact (1 ≤ p)] in
theorem convolutionValue_smul (k : Test) (c : ℂ) (f : Lp ℂ p (volume : Measure V)) (x : V) :
    convolutionValue k (c • f) x = c • convolutionValue k f x := by
  rw [convolutionValue, convolutionValue, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with y hy
  rw [hy]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Genuine bounded operator, so the full L-infinity realization respects ordinary Lp limits. -/
def convolutionInfinityCLM (k : Test) :
    Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ ∞ (volume : Measure V) :=
  LinearMap.mkContinuous
    { toFun := convolutionInfinity (r := r) k
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [convolutionInfinity_coe (r := r) k (f + g),
          convolutionInfinity_coe (r := r) k f, convolutionInfinity_coe (r := r) k g,
          Lp.coeFn_add (convolutionInfinity (r := r) k f) (convolutionInfinity (r := r) k g)]
          with x hsum hf hg htarget
        simp only [Pi.add_apply] at htarget
        rw [hsum, htarget, hf, hg]
        exact convolutionValue_add (r := r) k f g x
      map_smul' := by
        intro c f
        change convolutionInfinity (r := r) k (c • f) = c • convolutionInfinity (r := r) k f
        apply Lp.ext
        filter_upwards [convolutionInfinity_coe (r := r) k (c • f),
          convolutionInfinity_coe (r := r) k f,
          Lp.coeFn_smul c (convolutionInfinity (r := r) k f)] with x hcf hf htarget
        simp only [Pi.smul_apply] at htarget
        rw [hcf, htarget, hf]
        exact convolutionValue_smul k c f x }
    ‖k.toLp r volume‖ (convolutionInfinity_norm (r := r) k)

theorem convolutionInfinityCLM_apply (k : Test) (f : Lp ℂ p (volume : Measure V)) :
    convolutionInfinityCLM (r := r) k f = convolutionInfinity (r := r) k f := rfl

theorem convolutionInfinityCLM_norm (k : Test) :
    ‖convolutionInfinityCLM (p := p) (r := r) k‖ ≤ ‖k.toLp r volume‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end HartreeF.PhysicalLowpass
