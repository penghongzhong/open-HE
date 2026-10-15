import FPhysicalConvolutionDistribution
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap ZeroAtInfty
namespace HartreeF.Paper121ConvolutionC0
open EnergySpace PhysicalLowpass

def evaluationC0 (x : V) : C₀(V, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by
      change ‖f x‖ ≤ 1*‖f‖
      rw [one_mul, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact f.toBCF.norm_coe_le_norm x)

variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] [p.HolderConjugate r]

def convolutionEvaluation (k : Test) (x : V) : Lp ℂ p (volume : Measure V) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => convolutionValue k f x
      map_add' := fun f g => convolutionValue_add (r := r) k f g x
      map_smul' := fun c f => convolutionValue_smul k c f x }
    ‖k.toLp r volume‖ (fun f => convolutionValue_norm (r := r) k f x)

def schwartzConvolutionC0 (k : Test) : Test →L[ℂ] C₀(V, ℂ) :=
  (SchwartzMap.toZeroAtInftyCLM ℂ V ℂ).comp
    (SchwartzMap.fourierMultiplierCLM ℂ (𝓕 k : Test))

theorem schwartzConvolutionC0_bound (k φ : Test) :
    ‖schwartzConvolutionC0 k φ‖ ≤ ‖k.toLp r volume‖*‖φ.toLp p volume‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro x
  change ‖SchwartzMap.fourierMultiplierCLM ℂ (𝓕 k : Test) φ x‖ ≤ _
  rw [← convolutionValue_schwartz (p := p) k φ x]
  exact convolutionValue_norm (r := r) k (φ.toLp p volume) x

/-- Extension into the complete C0 space; no C0 premise on the Lp input. -/
def convolutionC0 (k : Test) : Lp ℂ p (volume : Measure V) →L[ℂ] C₀(V, ℂ) :=
  (schwartzConvolutionC0 k).toLinearMap.extendOfNorm (SchwartzMap.toLpCLM ℂ ℂ p volume).toLinearMap

include r in
theorem convolutionC0_schwartz (hp : p ≠ ∞) (k φ : Test) :
    convolutionC0 (p := p) k (φ.toLp p volume) = schwartzConvolutionC0 k φ := by
  apply LinearMap.extendOfNorm_eq
  · exact SchwartzMap.denseRange_toLpCLM hp
  · exact ⟨‖k.toLp r volume‖, fun ψ => schwartzConvolutionC0_bound (p := p) (r := r) k ψ⟩

include r in
theorem convolutionC0_apply (hp : p ≠ ∞) (k : Test)
    (f : Lp ℂ p (volume : Measure V)) (x : V) :
    convolutionC0 (p := p) k f x = convolutionValue k f x := by
  have he := (SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := V) (p := p)
    (μ := (volume : Measure V)) hp).equalizer
    ((evaluationC0 x).continuous.comp (convolutionC0 (p := p) k).continuous)
    (convolutionEvaluation (p := p) (r := r) k x).continuous (by
      funext φ
      change convolutionC0 (p := p) k (φ.toLp p volume) x =
        convolutionValue k (φ.toLp p volume) x
      rw [convolutionC0_schwartz (r := r) hp]
      exact (convolutionValue_schwartz (p := p) k φ x).symm)
  exact congrFun he f

theorem convolutionC0_bound (hp : p ≠ ∞) (k : Test) :
    ‖convolutionC0 (p := p) k‖ ≤ ‖k.toLp r volume‖ := by
  apply LinearMap.opNorm_extendOfNorm_le
  · exact SchwartzMap.denseRange_toLpCLM hp
  · exact norm_nonneg _
  · exact fun ψ => schwartzConvolutionC0_bound (p := p) (r := r) k ψ

include r in
/-- The everywhere-defined actual integral is continuous and vanishes at infinity. -/
theorem actual_convolution_continuous_vanishing (hp : p ≠ ∞) (k : Test)
    (f : Lp ℂ p (volume : Measure V)) :
    Continuous (convolutionValue k f) ∧
      Tendsto (convolutionValue k f) (cocompact V) (𝓝 0) := by
  have he : convolutionValue k f = (convolutionC0 (p := p) k f : V → ℂ) :=
    (funext (convolutionC0_apply (r := r) hp k f)).symm
  rw [he]
  exact ⟨map_continuous _, zero_at_infty _⟩

end HartreeF.Paper121ConvolutionC0
