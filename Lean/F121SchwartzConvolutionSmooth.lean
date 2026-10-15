import F121SchwartzConvolutionDerivative
import F121CutoffCore

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Paper121SmoothConvolution
open EnergySpace PhysicalLowpass YoungSource

/-- All finite derivative orders, for the same literal integral and the same weight. -/
theorem kernelIntegral_contDiff_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (n : ℕ) (k : 𝓢(V, E)) {f : V → ℂ} (hf : AEStronglyMeasurable f volume) {d : ℕ}
    (hw : Integrable (fun y : V => ‖f y‖*(1+‖y‖)^(-(d : ℝ))) volume) :
    ContDiff ℝ (n : ℕ∞) (kernelIntegral k f) := by
  induction n generalizing E with
  | zero =>
    rw [contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun x => (kernelIntegral_hasFDerivAt k hf hw x).continuousAt
  | succ n ih =>
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨kernelIntegral (SchwartzMap.fderivCLM ℂ V E k) f,
      ih _ hf hw, kernelIntegral_hasFDerivAt k hf hw⟩

theorem kernelIntegral_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (k : 𝓢(V, E)) {f : V → ℂ} (hf : AEStronglyMeasurable f volume) {d : ℕ}
    (hw : Integrable (fun y : V => ‖f y‖*(1+‖y‖)^(-(d : ℝ))) volume) :
    ContDiff ℝ (⊤ : ℕ∞) (kernelIntegral k f) :=
  contDiff_infty.mpr fun n => kernelIntegral_contDiff_nat n k hf hw

/-- No smoothness or decay premise on the Lp input; every spatial point is covered. -/
theorem actual_convolution_smooth {p r : ℝ≥0∞} [p.HolderConjugate r]
    (k : Test) (f : Lp ℂ p (volume : Measure V)) :
    ContDiff ℝ (⊤ : ℕ∞) (convolutionValue k f) := by
  obtain ⟨d, hd⟩ := lp_weight_integrable (r := r) f
  exact kernelIntegral_smooth k (Lp.aestronglyMeasurable f) hd

local instance : (6 : ℝ≥0∞).HolderConjugate sourceExponent := by
  have h : Real.HolderConjugate 6 (6/5) := by norm_num [Real.holderConjugate_iff]
  simpa [sourceExponent] using h.ennrealOfReal

theorem low_convolution_smooth (q : EnergySpace.Highpass.Cutoff) {M : ℝ} (hM : 0 < M)
    (u : EnergyState) :
    ContDiff ℝ (⊤ : ℕ∞) (convolutionValue (cutoffKernel q hM) (energyValue u)) :=
  actual_convolution_smooth (r := sourceExponent) _ _

end HartreeF.Paper121SmoothConvolution
