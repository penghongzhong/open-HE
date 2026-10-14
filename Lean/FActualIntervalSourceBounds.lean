import FCriticalHartreeSourceSmallness
import FIntervalHartreeSources

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.CriticalSourceBounds
open EnergySpace CriticalPathSpace CriticalTimeSobolev TimeHolder SobolevStretch
open StationarySelfTest ForcingDomain GradientMajorants WeakHartreeProduct CriticalJointSources
open ActualDuhamelPath IntervalTimeTransport Retarded
attribute [local irreducible] jointFields energySubmodule criticalPathSubmodule
  energyPath criticalGradient energyValue energyGradient
local instance endpointSourceExponent_one_le : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩

theorem endpointGradientCoordinate_norm_le (j : Fin 3) : ‖endpointGradientCoordinate j‖ ≤ 1 := by
  apply (ContinuousLinearMap.norm_compLpL_le _).trans
  apply ContinuousLinearMap.opNorm_le_bound (EuclideanSpace.proj (𝕜 := ℂ) j) (by norm_num)
  intro v
  simpa only [EuclideanSpace.coe_proj, one_mul] using PiLp.norm_apply_le v j

theorem endpointGradientCoordinateSource_norm_le {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (j : Fin 3)
    (G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 μ) : ‖endpointGradientCoordinateSource μ j G‖ ≤ ‖G‖ := by
  exact ((endpointGradientCoordinate j).norm_compLp_le G).trans
    ((mul_le_mul_of_nonneg_right (endpointGradientCoordinate_norm_le j) (norm_nonneg _)).trans_eq (one_mul _))

/-- No transport or spatial projection loss in each actual source coordinate. -/
theorem criticalPathIntervalSource_gradient_enorm_le (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (z w : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ‖(criticalPathIntervalSource hDensity hSob hH hab z w).gradient j‖ₑ ≤
      actualGradientSize (intervalMeasure a b) alpha c z w := by
  let Gs := Classical.choose (exists_joint_actualGradient_source (intervalMeasure a b) hDensity hSob hH z w)
  have hGs := (Classical.choose_spec (exists_joint_actualGradient_source (intervalMeasure a b) hDensity hSob hH z w)).2
  change ‖endpointGradientCoordinateSource (localMeasure a b) j (toLocalLp hab 2 Gs)‖ₑ ≤ _
  calc
    _ ≤ ‖toLocalLp hab 2 Gs‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (endpointGradientCoordinateSource_norm_le _ j _)
    _ = ‖Gs‖ₑ := by simp only [← ofReal_norm, toLocalLp_norm]
    _ = _ := hGs

attribute [local irreducible] criticalPathIntervalSource

theorem criticalPathIntervalSource_uniform_smallness (hDensity : OrdinaryH1Density)
    {K alpha c B epsilon : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
    (z w : CriticalPath (intervalMeasure a b)),
    pathEnergySize (intervalMeasure a b) z + pathEnergySize (intervalMeasure a b) w ≤ ENNReal.ofReal B →
    pathValueSize (intervalMeasure a b) z + pathValueSize (intervalMeasure a b) w ≤ ENNReal.ofReal eta →
    pathGradientSize (intervalMeasure a b) w ≤ ENNReal.ofReal eta →
    ∀ j : Fin 3, ‖(criticalPathIntervalSource hDensity hSob hH hab z w).gradient j‖ ≤ epsilon * ‖z-w‖ := by
  let hExist := actualGradientSize_uniform_smallness hDensity hSob hH hB hepsilon
  let eta : ℝ := Classical.choose hExist
  refine ⟨eta, (Classical.choose_spec hExist).1, (Classical.choose_spec hExist).2.1, ?_⟩
  intro a b hab z w hM hN hY j
  have hb := (criticalPathIntervalSource_gradient_enorm_le hDensity hSob hH hab z w j).trans
    ((Classical.choose_spec hExist).2.2 (T := Set.Icc a b) (intervalMeasure a b) z w hM hN hY)
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb
  simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hepsilon.le] using hr

/-- The actual source bound on the native energy/critical-coordinate cap. -/
theorem criticalPathIntervalSource_cap_uniform_smallness (hDensity : OrdinaryH1Density)
    {K alpha c B epsilon : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
    (z w : CriticalPath (intervalMeasure a b)),
    ‖energyPath (intervalMeasure a b) z‖ ≤ B → ‖energyPath (intervalMeasure a b) w‖ ≤ B →
    ‖fun j => criticalGradient (intervalMeasure a b) j z‖ ≤ eta →
    ‖fun j => criticalGradient (intervalMeasure a b) j w‖ ≤ eta →
    ∀ j : Fin 3, ‖(criticalPathIntervalSource hDensity hSob hH hab z w).gradient j‖ ≤ epsilon * ‖z-w‖ := by
  let hExist := actualGradientSize_cap_uniform_smallness hDensity hSob hH hB hepsilon
  let eta : ℝ := Classical.choose hExist
  refine ⟨eta, (Classical.choose_spec hExist).1, (Classical.choose_spec hExist).2.1, ?_⟩
  intro a b hab z w hM hN hY hZ j
  have hb := (criticalPathIntervalSource_gradient_enorm_le hDensity hSob hH hab z w j).trans
    ((Classical.choose_spec hExist).2.2 (T := Set.Icc a b) (intervalMeasure a b) z w hM hN hY hZ)
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hb
  simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hepsilon.le] using hr

/-- A single finite constant is selected before the interval or path.
The explicit fifth-power gain makes the later self-map choice noncircular. -/
theorem criticalPathIntervalSource_cap_single_bound (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ {a b : ℝ} (hab : a ≤ b) (z : CriticalPath (intervalMeasure a b))
    (B eta : ℝ) (_ : 0 ≤ B) (_ : 0 ≤ eta),
    ‖energyPath (intervalMeasure a b) z‖ ≤ B →
    ‖fun j => criticalGradient (intervalMeasure a b) j z‖ ≤ eta →
    ∀ j : Fin 3, ‖(criticalPathIntervalSource hDensity hSob hH hab z 0).gradient j‖ ≤
      (C : ℝ) * B^(2*alpha) * (normComparisonConstant K)^5 * eta^5 := by
  let hExist := actualGradientSize_single_bound hDensity hSob hH
  let C : ℝ≥0 := Classical.choose hExist
  refine ⟨C, ?_⟩
  intro a b hab z B eta hB heta hE hG j
  have hz := path_sizes_le_coordinate_cap (intervalMeasure a b) hDensity hSob heta z hG
  have hM := (joint_value_energy_projection_bound (intervalMeasure a b) z).trans
    (ENNReal.ofReal_le_ofReal hE)
  have hb := (criticalPathIntervalSource_gradient_enorm_le hDensity hSob hH hab z 0 j).trans
    ((Classical.choose_spec hExist) (intervalMeasure a b) z (ENNReal.ofReal B) (ENNReal.ofReal (normComparisonConstant K * eta)) hM hz.2 hz.1)
  have hf : (C : ℝ≥0∞) * (ENNReal.ofReal B)^(2*alpha) *
      (ENNReal.ofReal (normComparisonConstant K * eta))^(5 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH.order_pos.le) ENNReal.ofReal_ne_top))
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hr := ENNReal.toReal_mono hf hb
  have hL := (normComparisonConstant_pos hSob).le
  simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.coe_toReal, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal (mul_nonneg hL heta), Real.rpow_ofNat, mul_pow, mul_assoc] using hr

end HartreeF.CriticalSourceBounds
