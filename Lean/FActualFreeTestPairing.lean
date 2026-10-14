import FActualFreeTestL6Bound
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter FourierTransform
open scoped ENNReal Topology
namespace HartreeF.FreeTestBounds
open Retarded EnergySpace SobolevStretch StationarySelfTest
local instance : ENNReal.HolderConjugate 6 (ENNReal.ofReal (6/5 : ℝ)) := ⟨by
  have hq : ENNReal.ofReal (6/5 : ℝ) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 6/5)).ne'
  have hqi : (ENNReal.ofReal (6/5 : ℝ))⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hq
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.add_ne_top.mpr ⟨by simp, hqi⟩) (by simp)).mp
  rw [ENNReal.toReal_add (by simp) hqi]
  norm_num⟩

/-- The genuine spatial L6--L6/5 bilinear integral as a continuous map. -/
def sourcePairCLM : EnergySpace.L6 →L[ℂ] SourceSpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 6 (ENNReal.ofReal (6/5 : ℝ))

theorem sourcePairCLM_test (φ : FreeFlow.Test) (f : SourceSpace) :
    sourcePairCLM (φ.toLp 6 volume) f = Lp.toTemperedDistribution f φ := by
  rw [sourcePairCLM, ContinuousLinearMap.lpPairing_eq_integral,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 6 volume] with x hx
  simp only [ContinuousLinearMap.mul_apply', hx, smul_eq_mul]

theorem freeTest_L6_continuous (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (φ : FreeFlow.Test) :
    Continuous (fun t : ℝ => (freeTest t φ).toLp 6 volume) := by
  have h := energyValue.continuous.comp
    (freeEnergyState_time_continuous hDensity hSob (schwartzEnergyState φ))
  simpa only [Function.comp_def, freeEnergyState_schwartz,
    schwartzEnergyState_value, freeTest_eq_freeSchwartz] using h

theorem freeTestPair_norm_le (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (t : ℝ) (φ : FreeFlow.Test) (f : SourceSpace) :
    ‖Lp.toTemperedDistribution f (freeTest t φ)‖ ≤
      (‖sourcePairCLM‖ * (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm (schwartzEnergyState φ))) * ‖f‖ := by
  rw [← sourcePairCLM_test]
  exact (sourcePairCLM.le_opNorm₂ _ _).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (freeTest_L6_norm_le hDensity hSob t φ)
        (norm_nonneg sourcePairCLM))
      (norm_nonneg f))

/-- True scalar integrability is proved before using its Bochner integral. -/
theorem freeTestPair_integrable (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (μ : Measure ℝ) (t : ℝ) (φ : FreeFlow.Test)
    (f : ℝ → SourceSpace) (hf : Integrable f μ) :
    Integrable (fun s => Lp.toTemperedDistribution (f s) (freeTest (t-s) φ)) μ := by
  let P : ℝ → EnergySpace.L6 := fun s => (freeTest (t-s) φ).toLp 6 volume
  have hP : Continuous P := (freeTest_L6_continuous hDensity hSob φ).comp
    (continuous_const.sub continuous_id)
  have hi := sourcePairCLM.integrable_of_bilin_of_bdd_left
    (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm (schwartzEnergyState φ))
    hP.aestronglyMeasurable
    (Eventually.of_forall (fun s => freeTest_L6_norm_le hDensity hSob (t-s) φ)) hf
  exact hi.congr (Eventually.of_forall (fun s => sourcePairCLM_test (freeTest (t-s) φ) (f s)))

/-- The actual scalar integral is quantitatively continuous in the genuine
L1 source value, uniformly in the observation time. -/
theorem freeTestPair_integral_sub_norm_le (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (μ : Measure ℝ) (t : ℝ) (φ : FreeFlow.Test)
    (f g : ℝ → SourceSpace) (hf : Integrable f μ) (hg : Integrable g μ) :
    ‖(∫ s, Lp.toTemperedDistribution (f s) (freeTest (t-s) φ) ∂μ) -
      ∫ s, Lp.toTemperedDistribution (g s) (freeTest (t-s) φ) ∂μ‖ ≤
      (‖sourcePairCLM‖ * (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm (schwartzEnergyState φ))) *
        (eLpNorm (fun s => f s-g s) 1 μ).toReal := by
  let C : ℝ := ‖sourcePairCLM‖ * (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm (schwartzEnergyState φ))
  have hiF := freeTestPair_integrable hDensity hSob μ t φ f hf
  have hiG := freeTestPair_integrable hDensity hSob μ t φ g hg
  have hiD := freeTestPair_integrable hDensity hSob μ t φ (fun s => f s-g s) (hf.sub hg)
  have he (s : ℝ) :
      Lp.toTemperedDistribution (f s) (freeTest (t-s) φ) -
        Lp.toTemperedDistribution (g s) (freeTest (t-s) φ) =
          Lp.toTemperedDistribution (f s-g s) (freeTest (t-s) φ) := by
    rw [← sourcePairCLM_test, ← sourcePairCLM_test, ← sourcePairCLM_test]
    exact ((sourcePairCLM ((freeTest (t-s) φ).toLp 6 volume)).map_sub (f s) (g s)).symm
  rw [← integral_sub hiF hiG]
  simp_rw [he]
  calc
    _ ≤ ∫ s, ‖Lp.toTemperedDistribution (f s-g s) (freeTest (t-s) φ)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s, C * ‖f s-g s‖ ∂μ :=
      integral_mono_ae hiD.norm ((hf.sub hg).norm.const_mul C)
        (Eventually.of_forall (fun s => freeTestPair_norm_le hDensity hSob (t-s) φ (f s-g s)))
    _ = C * ∫ s, ‖f s-g s‖ ∂μ := integral_const_mul _ _
    _ = C * (eLpNorm (fun s => f s-g s) 1 μ).toReal := by
      have hm : AEStronglyMeasurable (fun s => f s-g s) μ := (hf.sub hg).aestronglyMeasurable
      rw [integral_norm_eq_lintegral_enorm hm, eLpNorm_one_eq_lintegral_enorm hm]

theorem freeTestPair_integral_tendsto_of_L1 (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (μ : Measure ℝ) (t : ℝ) (φ : FreeFlow.Test)
    (f : ℕ → ℝ → SourceSpace) (g : ℝ → SourceSpace)
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hlim : Tendsto (fun n => eLpNorm (fun s => f n s-g s) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ s, Lp.toTemperedDistribution (f n s) (freeTest (t-s) φ) ∂μ)
      atTop (𝓝 (∫ s, Lp.toTemperedDistribution (g s) (freeTest (t-s) φ) ∂μ)) := by
  have hr : Tendsto (fun n => (eLpNorm (fun s => f n s-g s) 1 μ).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => freeTestPair_integral_sub_norm_le hDensity hSob μ t φ (f n) g (hf n) hg)
  simpa only [mul_zero] using hr.const_mul
    (‖sourcePairCLM‖ * (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm (schwartzEnergyState φ)))

set_option pp.universes true
#check @sourcePairCLM
#print axioms sourcePairCLM
#check @sourcePairCLM_test
#print axioms sourcePairCLM_test
#check @freeTest_L6_continuous
#print axioms freeTest_L6_continuous
#check @freeTestPair_norm_le
#print axioms freeTestPair_norm_le
#check @freeTestPair_integrable
#print axioms freeTestPair_integrable
#check @freeTestPair_integral_sub_norm_le
#print axioms freeTestPair_integral_sub_norm_le
#check @freeTestPair_integral_tendsto_of_L1
#print axioms freeTestPair_integral_tendsto_of_L1
end HartreeF.FreeTestBounds
