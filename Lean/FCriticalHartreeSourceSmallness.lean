import FCriticalPathQuantitativeNorms
import FActualGradientUniformSmallness
import FCriticalPathSourceBudgets

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.CriticalSourceBounds
open EnergySpace CriticalPathSpace CriticalTimeSobolev TimeHolder SobolevStretch
open StationarySelfTest ForcingDomain GradientMajorants WeakHartreeProduct CriticalJointSources
attribute [local irreducible] jointFields energySubmodule criticalPathSubmodule
  energyPath criticalGradient energyValue energyGradient

abbrev actualGradientSize {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (alpha c : ℝ) (z w : CriticalPath μ) : ℝ≥0∞ :=
  mixedNorm μ volume 2 (ENNReal.ofReal (6/5 : ℝ))
    (fun t => actualFullGradient alpha c ((jointFields μ z).u t) ((jointFields μ z).U t)
      ((jointFields μ z).V t) - actualFullGradient alpha c ((jointFields μ w).u t)
      ((jointFields μ w).U t) ((jointFields μ w).V t))

def normComparisonConstant (K : ℝ) : ℝ := 7 + ((5/3)*K^(1/6 : ℝ))*6

theorem normComparisonConstant_eq (K : ℝ) :
    normComparisonConstant K = 7 + 10 * K^(1/6 : ℝ) := by
  unfold normComparisonConstant
  ring

theorem normComparisonConstant_pos {K : ℝ} (hSob : OrdinarySobolev K) :
    0 < normComparisonConstant K := by
  have hK := hSob.nonneg
  unfold normComparisonConstant
  positivity

section UniformSource
attribute [local irreducible] pathGradientSize pathValueSize pathEnergySize

/-- The uniform threshold is chosen before the time space, measure and paths.
The difference metric is the actual complete path norm. -/
theorem actualGradientSize_uniform_smallness (hDensity : OrdinaryH1Density)
    {K alpha c B epsilon : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure T) [SigmaFinite μ] (z w : CriticalPath μ),
    pathEnergySize μ z + pathEnergySize μ w ≤ ENNReal.ofReal B →
    pathValueSize μ z + pathValueSize μ w ≤ ENNReal.ofReal eta →
    pathGradientSize μ w ≤ ENNReal.ofReal eta →
    actualGradientSize μ alpha c z w ≤ ENNReal.ofReal epsilon * ENNReal.ofReal ‖z-w‖ := by
  let L := normComparisonConstant K
  have hL : 0 < L := normComparisonConstant_pos hSob
  have hK := hSob.nonneg
  have hS : 0 ≤ (5/3 : ℝ)*K^(1/6 : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ L := by dsimp [L, normComparisonConstant]; linarith
  have h6 : (6 : ℝ) ≤ L := by dsimp [L, normComparisonConstant]; linarith
  have hS6 : ((5/3 : ℝ)*K^(1/6 : ℝ))*6 ≤ L := by dsimp [L, normComparisonConstant]; linarith
  let hExist := actual_full_gradient_uniform_smallness hH hB (div_pos hepsilon hL)
  let eta : ℝ := Classical.choose hExist
  have heta : 0 < eta := (Classical.choose_spec hExist).1
  have heta1 : eta ≤ 1 := (Classical.choose_spec hExist).2.1
  refine ⟨eta, heta, heta1, ?_⟩
  intro T _ _ _ _ μ _ z w hM hN hY
  let delta := ENNReal.ofReal L * ENNReal.ofReal ‖z-w‖
  have hD := (joint_value_difference_energy_bound μ z w).trans
    (show ENNReal.ofReal ‖z-w‖ ≤ delta from by
      calc
        _ = 1 * ENNReal.ofReal ‖z-w‖ := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal h1) le_rfl)
  have hZ := (joint_gradient_difference_bound μ z w).trans
    (mul_le_mul' (show (6 : ℝ≥0∞) ≤ ENNReal.ofReal L by simpa using ENNReal.ofReal_le_ofReal h6) le_rfl)
  have hE := (joint_value_difference_critical_bound μ hDensity hSob z w).trans
    (mul_le_mul' (show ENNReal.ofReal ((5/3)*K^(1/6 : ℝ)) * 6 ≤ ENNReal.ofReal L by
      simpa only [ENNReal.ofReal_mul hS, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hS6) le_rfl)
  have hh := (Classical.choose_spec hExist).2.2 (T := T) μ delta (jointFields μ z).u (jointFields μ w).u
    (jointFields μ z).U (jointFields μ z).V (jointFields μ w).U (jointFields μ w).V
    (joint_slices μ hDensity hSob z w)
    (jointFields μ z).joint_u.aestronglyMeasurable (jointFields μ w).joint_u.aestronglyMeasurable
    (jointFields μ z).joint_U.aestronglyMeasurable (jointFields μ z).joint_V.aestronglyMeasurable
    (jointFields μ w).joint_U.aestronglyMeasurable (jointFields μ w).joint_V.aestronglyMeasurable
    (by simpa only [pathEnergySize] using hM)
    (by simpa only [pathValueSize] using hN)
    (by simpa only [pathGradientSize] using hY) hD hE hZ
  have hc : ENNReal.ofReal (epsilon / L) * ENNReal.ofReal L = ENNReal.ofReal epsilon := by
    rw [← ENNReal.ofReal_mul (div_pos hepsilon hL).le, div_mul_cancel₀ epsilon hL.ne']
  exact hh.trans_eq (by dsimp [delta]; rw [← mul_assoc, hc])



end UniformSource

theorem criticalBudget_zero_comparison (alpha : ℝ) (M N D E Z : ℝ≥0∞) :
    criticalBudget alpha M N D E 0 Z = M^(2*alpha) * N^(4 : ℝ) * Z := by
  simp only [criticalBudget, mul_zero, zero_mul, add_zero]

@[simp] theorem pathGradientSize_zero {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] : pathGradientSize μ (0 : CriticalPath μ) = 0 := by
  have hn : ENNReal.ofReal ‖(0 : CriticalPath μ)‖ = 0 :=
    (congrArg ENNReal.ofReal (_root_.norm_zero (E := CriticalPath μ))).trans ENNReal.ofReal_zero
  exact le_antisymm ((joint_gradient_bound μ (0 : CriticalPath μ)).trans_eq
    ((congrArg (fun x : ℝ≥0∞ => 6*x) hn).trans (mul_zero 6))) bot_le

@[simp] theorem pathEnergySize_zero {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] : pathEnergySize μ (0 : CriticalPath μ) = 0 := by
  have hn : ENNReal.ofReal ‖(0 : CriticalPath μ)‖ = 0 :=
    (congrArg ENNReal.ofReal (_root_.norm_zero (E := CriticalPath μ))).trans ENNReal.ofReal_zero
  exact le_antisymm ((joint_value_energy_bound μ (0 : CriticalPath μ)).trans_eq hn) bot_le

theorem pathValueSize_zero {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) : pathValueSize μ (0 : CriticalPath μ) = 0 := by
  exact le_antisymm ((joint_value_critical_bound μ hDensity hSob (0 : CriticalPath μ)).trans_eq
    ((congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal ((5/3)*K^(1/6 : ℝ))*x)
      (pathGradientSize_zero μ)).trans (mul_zero _))) bot_le

theorem joint_vectorBudget_single {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (hDensity : OrdinaryH1Density) {K alpha : ℝ}
    (hSob : OrdinarySobolev K) (z : CriticalPath μ) :
    vectorDifferenceBudget alpha μ (jointFields μ z).u (jointFields μ (0 : CriticalPath μ)).u
      (jointFields μ z).U (jointFields μ z).V
      (jointFields μ (0 : CriticalPath μ)).U (jointFields μ (0 : CriticalPath μ)).V =
      pathEnergySize μ z ^ (2*alpha) * pathValueSize μ z ^ (4 : ℝ) * pathGradientSize μ z := by
  have hz := pathGradientSize_zero μ
  have hM := pathEnergySize_zero μ
  have hN := pathValueSize_zero μ hDensity hSob
  have hZ :
      mixedNorm μ volume 10 criticalExponent (fun t => (jointFields μ z).U t - (jointFields μ (0 : CriticalPath μ)).U t) +
      mixedNorm μ volume 10 criticalExponent (fun t => (jointFields μ z).V t - (jointFields μ (0 : CriticalPath μ)).V t) =
      pathGradientSize μ z := by
    have hU := mixedNorm_congr_slices μ 10 criticalExponent ((joint_sub_slices μ z 0).mono fun _ ht => ht.2.1)
    have hV := mixedNorm_congr_slices μ 10 criticalExponent ((joint_sub_slices μ z 0).mono fun _ ht => ht.2.2)
    exact (congrArg₂ (fun x y : ℝ≥0∞ => x+y) hU.symm hV.symm).trans
      (congrArg (pathGradientSize μ) (sub_zero z))
  let D := mixedNorm μ volume ∞ 6 (fun t => (jointFields μ z).u t - (jointFields μ (0 : CriticalPath μ)).u t)
  let E := mixedNorm μ volume 10 10 (fun t => (jointFields μ z).u t - (jointFields μ (0 : CriticalPath μ)).u t)
  let Z := mixedNorm μ volume 10 criticalExponent (fun t => (jointFields μ z).U t - (jointFields μ (0 : CriticalPath μ)).U t) +
      mixedNorm μ volume 10 criticalExponent (fun t => (jointFields μ z).V t - (jointFields μ (0 : CriticalPath μ)).V t)
  have hMsum : pathEnergySize μ z + pathEnergySize μ 0 = pathEnergySize μ z :=
    (congrArg (fun x => pathEnergySize μ z + x) hM).trans (add_zero _)
  have hNsum : pathValueSize μ z + pathValueSize μ 0 = pathValueSize μ z :=
    (congrArg (fun x => pathValueSize μ z + x) hN).trans (add_zero _)
  have hfirst := congrArg₂ (fun M N => criticalBudget alpha M N D E (pathGradientSize μ 0) Z) hMsum hNsum
  have hlast := congrArg₂ (fun Y Z => criticalBudget alpha (pathEnergySize μ z) (pathValueSize μ z) D E Y Z) hz hZ
  exact hfirst.trans (hlast.trans (criticalBudget_zero_comparison alpha _ _ D E _))

/-- Exact fifth power single-source estimate; no circular smallness condition. -/
theorem actualGradientSize_single_bound (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure T) [SigmaFinite μ] (z : CriticalPath μ) (B eta : ℝ≥0∞),
    pathEnergySize μ z ≤ B → pathValueSize μ z ≤ eta → pathGradientSize μ z ≤ eta →
    actualGradientSize μ alpha c z 0 ≤ (C : ℝ≥0∞) * B^(2*alpha) * eta^(5 : ℝ) := by
  let hExist := actual_full_gradient_vector_difference_bound hH
  let C : ℝ≥0 := Classical.choose hExist
  refine ⟨C, ?_⟩
  intro T _ _ _ _ μ _ z B eta hM hN hW
  have hb := (Classical.choose_spec hExist) μ (jointFields μ z).u (jointFields μ (0 : CriticalPath μ)).u
    (jointFields μ z).U (jointFields μ z).V (jointFields μ (0 : CriticalPath μ)).U (jointFields μ (0 : CriticalPath μ)).V
    (joint_slices μ hDensity hSob z 0)
    (jointFields μ z).joint_u.aestronglyMeasurable (jointFields μ (0 : CriticalPath μ)).joint_u.aestronglyMeasurable
    (jointFields μ z).joint_U.aestronglyMeasurable (jointFields μ z).joint_V.aestronglyMeasurable
    (jointFields μ (0 : CriticalPath μ)).joint_U.aestronglyMeasurable (jointFields μ (0 : CriticalPath μ)).joint_V.aestronglyMeasurable
  have hsingle := hb.trans_eq (congrArg (fun x : ℝ≥0∞ => (C : ℝ≥0∞)*x)
    (joint_vectorBudget_single μ hDensity hSob z))
  have hm := ENNReal.rpow_le_rpow hM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH.order_pos.le)
  have hn := ENNReal.rpow_le_rpow hN (by norm_num : (0 : ℝ) ≤ 4)
  apply hsingle.trans
  calc
    _ ≤ (C : ℝ≥0∞) * (B^(2*alpha) * eta^(4 : ℝ) * eta) :=
      mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' hm hn) hW)
    _ = _ := by rw [show (5 : ℝ) = 4+1 by norm_num, ENNReal.rpow_add_of_nonneg 4 1 (by norm_num) (by norm_num)]; simp only [ENNReal.rpow_one]; ring


/-- A critical-coordinate cap controls both real/imaginary W and scalar S. -/
theorem path_sizes_le_coordinate_cap {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (hDensity : OrdinaryH1Density) {K eta : ℝ}
    (hSob : OrdinarySobolev K) (heta : 0 ≤ eta) (z : CriticalPath μ)
    (hz : ‖fun j => criticalGradient μ j z‖ ≤ eta) :
    pathGradientSize μ z ≤ ENNReal.ofReal (normComparisonConstant K * eta) ∧
    pathValueSize μ z ≤ ENNReal.ofReal (normComparisonConstant K * eta) := by
  have hK := hSob.nonneg
  have hS : 0 ≤ (5/3 : ℝ)*K^(1/6 : ℝ) := by positivity
  have hW : pathGradientSize μ z ≤ ENNReal.ofReal (6*eta) := by
    have hb := (joint_gradient_projection_bound μ z).trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hz))
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat] using hb
  have h6 : (6 : ℝ) ≤ normComparisonConstant K := by unfold normComparisonConstant; linarith
  have hS6 : ((5/3 : ℝ)*K^(1/6 : ℝ))*6 ≤ normComparisonConstant K := by unfold normComparisonConstant; linarith
  refine ⟨hW.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h6 heta)), ?_⟩
  have hv := (joint_value_critical_bound μ hDensity hSob z).trans (mul_le_mul' le_rfl hW)
  rw [← ENNReal.ofReal_mul hS, ← mul_assoc] at hv
  exact hv.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hS6 heta))

/-- Uniform small Lipschitz coefficient on the true energy/coordinate cap.
The threshold is independent of interval and paths, including zero measure. -/
theorem actualGradientSize_cap_uniform_smallness (hDensity : OrdinaryH1Density)
    {K alpha c B epsilon : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    (ν : Measure T) [SigmaFinite ν] (z w : CriticalPath ν),
    ‖energyPath ν z‖ ≤ B → ‖energyPath ν w‖ ≤ B →
    ‖fun j => criticalGradient ν j z‖ ≤ eta → ‖fun j => criticalGradient ν j w‖ ≤ eta →
    actualGradientSize ν alpha c z w ≤ ENNReal.ofReal epsilon * ENNReal.ofReal ‖z-w‖ := by
  let L := normComparisonConstant K
  have hL : 0 < L := normComparisonConstant_pos hSob
  let hExist := actualGradientSize_uniform_smallness hDensity hSob hH
    (show 0 ≤ 2*B by positivity) hepsilon
  let rho : ℝ := Classical.choose hExist
  have hrho : 0 < rho := (Classical.choose_spec hExist).1
  let eta := min 1 (rho/(2*L))
  have heta : 0 < eta := lt_min (by norm_num) (div_pos hrho (by positivity))
  have he : 2*L*eta ≤ rho := by
    have h : eta*(2*L) ≤ rho := (le_div_iff₀ (by positivity : 0 < 2*L)).mp (min_le_right _ _)
    nlinarith
  have hLE : 0 ≤ L*eta := mul_nonneg hL.le heta.le
  have hdouble : ENNReal.ofReal (L*eta) + ENNReal.ofReal (L*eta) ≤ ENNReal.ofReal rho :=
    (ENNReal.ofReal_add hLE hLE).symm.le.trans
      (ENNReal.ofReal_le_ofReal (show L*eta + L*eta ≤ rho by nlinarith))
  have hsingle : L*eta ≤ rho := by nlinarith
  have htwoB : ENNReal.ofReal B + ENNReal.ofReal B = ENNReal.ofReal (2*B) :=
    (ENNReal.ofReal_add hB hB).symm.trans (congrArg ENNReal.ofReal (show B+B = 2*B by ring))
  refine ⟨eta, heta, min_le_left _ _, ?_⟩
  intro T _ _ _ _ ν _ z w hzE hwE hzW hwW
  have hz := path_sizes_le_coordinate_cap ν hDensity hSob heta.le z hzW
  have hw := path_sizes_le_coordinate_cap ν hDensity hSob heta.le w hwW
  apply (Classical.choose_spec hExist).2.2 (T := T) ν z w
  · have hMz := (joint_value_energy_projection_bound ν z).trans (ENNReal.ofReal_le_ofReal hzE)
    have hMw := (joint_value_energy_projection_bound ν w).trans (ENNReal.ofReal_le_ofReal hwE)
    exact (add_le_add hMz hMw).trans_eq htwoB
  · exact (add_le_add hz.2 hw.2).trans hdouble
  · exact hw.1.trans (ENNReal.ofReal_le_ofReal hsingle)

end HartreeF.CriticalSourceBounds
