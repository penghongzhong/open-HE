import FWeightedRieszSliceAlgebra
import FSameStateWeightedHardy
import FBoundedSpatialBounds

/-! STATIC-ONLY CANDIDATE. Genuine scalar slice bounds on one original EnergyState.
The value need not be in L2. The coordinate gradient is the original state's L2 value.
The alpha=2 endpoint below invokes actual Hardy, never open-s interpolation. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeightedRieszProduct
open EnergySpace SobolevStretch StationarySelfTest SameStateHardy WeightedHardy
  GradientMajorants BoundedHartreeGradient

theorem value_power_aestronglyMeasurable (u : EnergyState) (p : ℝ) :
    AEStronglyMeasurable (fun x => ‖energyValue u x‖ ^ p) volume :=
  ((Lp.aestronglyMeasurable (energyValue u)).norm.aemeasurable.pow_const p).aestronglyMeasurable

theorem value_power_ae_bound {A p : ℝ} (u : EnergyState) (hp : 0 ≤ p)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A) :
    ∀ᵐ x ∂volume, ‖‖energyValue u x‖ ^ p‖ ≤ A ^ p := by
  filter_upwards [hA] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _) hx hp

/-- The actual coordinate gradient, bounded by the state's pure kinetic norm. -/
theorem coordinate_gradient_spatialBound (u : EnergyState) (j : Fin 3) :
    SpatialBound (fun x => ‖energyGradient j u x‖) (1 / 2) (pureGradientNorm u) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · simpa only [one_div_div, div_one, ENNReal.ofReal_ofNat] using
      (Lp.memLp (energyGradient j u)).norm
  · change (eLpNorm (fun x => ‖energyGradient j u x‖)
      (ENNReal.ofReal (1 / (1 / 2 : ℝ))) volume).toReal ≤ _
    rw [one_div_div, div_one, ENNReal.ofReal_ofNat,
      eLpNorm_norm _ (Lp.aestronglyMeasurable (energyGradient j u))]
    change ‖energyGradient j u‖ ≤ pureGradientNorm u
    exact energyGradient_le_pureGradient u j

/-- Closed Hardy endpoint on the same value. No original-value L2 premise. -/
theorem weightedDensity_one_spatialBound (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (y : V) (u : EnergyState) :
    SpatialBound (weightedDensity 1 y (energyValue u)) 1
      (weightedConstant K 1 (pureGradientNorm u)) := by
  have hb := (hardy_norm_spatialBound hDensity hSob y u).rpow
    (fun x => norm_nonneg (weightedValue y u x)) (by norm_num : (0 : ℝ) < 2)
  have hf : (fun x => ‖weightedValue y u x‖ ^ (2 : ℝ)) =
      weightedDensity 1 y (energyValue u) := by
    funext x
    simpa only [weightedDensity, show (6 - 4 * (1 : ℝ)) = 2 by norm_num,
      show (2 * (1 : ℝ)) = 2 by norm_num, Real.rpow_ofNat] using
      weightedValue_norm_sq y u x
  rw [hf] at hb
  convert hb using 1 <;> norm_num [weightedConstant]
  ring

/-- Derivative-kernel weighted density for the whole closed upper range.
The equality case alpha=2 is handled by the preceding genuine Hardy theorem. -/
theorem derivative_density_spatialBound (hDensity : OrdinaryH1Density)
    {K α : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (y : V) (u : EnergyState) :
    SpatialBound (weightedDensity ((4 - α) / 2) y (energyValue u)) 1
      (derivativeConstant K α (pureGradientNorm u)) := by
  rw [← derivative_weightedConstant]
  rcases eq_or_lt_of_le hα2 with hα | hα
  · subst α
    simpa only [show ((4 - 2) / 2 : ℝ) = 1 by norm_num] using
      weightedDensity_one_spatialBound hDensity hSob y u
  · exact weighted_density_spatialBound hDensity hSob (by linarith) (by linarith) y u

/-- The local-gradient Cauchy weight. Alpha=2 again uses genuine Hardy. -/
theorem local_density_spatialBound (hDensity : OrdinaryH1Density)
    {K α : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (y : V) (u : EnergyState) :
    SpatialBound (weightedDensity (3 - α) y (energyValue u)) 1
      (weightedConstant K (3 - α) (pureGradientNorm u)) := by
  rcases eq_or_lt_of_le hα2 with hα | hα
  · subst α
    simpa only [show (3 - 2 : ℝ) = 1 by norm_num] using
      weightedDensity_one_spatialBound hDensity hSob y u
  · exact weighted_density_spatialBound hDensity hSob (by linarith) (by linarith) y u

/-- Genuine Cauchy on the literal weighted value and actual coordinate gradient. -/
theorem local_cauchy_spatialBound (hDensity : OrdinaryH1Density)
    {K α : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (y : V) (u : EnergyState) (j : Fin 3) :
    SpatialBound
      (fun x => weightedDensity (3 - α) y (energyValue u) x ^ (1 / 2 : ℝ) *
        ‖energyGradient j u x‖) 1
      (localGradientConstant K α (pureGradientNorm u)) := by
  have hw := (local_density_spatialBound hDensity hSob hα2 hα3 y u).rpow
    (weightedDensity_nonneg _ _ _) (by norm_num : (0 : ℝ) < 1 / 2)
  have hh := hw.mul (coordinate_gradient_spatialBound u j)
  rw [local_gradient_weightedConstant hSob.nonneg (pureGradientNorm_nonneg u) hα2] at hh
  simpa only [show ((1 / 2 : ℝ) * 1 + 1 / 2) = 1 by norm_num] using hh

/-- Literal translated derivative-kernel slice: actual L1 domain and finite bound. -/
theorem derivativeSlice_spatialBound (hDensity : OrdinaryH1Density)
    {K α A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A) (y : V) :
    SpatialBound (derivativeSlice α u y) 1
      (A ^ (4 - α) * derivativeConstant K α (pureGradientNorm u)) := by
  have hb := spatialBound_mul_bounded
    (derivative_density_spatialBound hDensity hSob hα2 hα3 y u)
    (value_power_aestronglyMeasurable u (4 - α)) (Real.rpow_nonneg hA0 _)
    (value_power_ae_bound u (by linarith : 0 ≤ 4 - α) hA)
  have hf : (fun x => ‖energyValue u x‖ ^ (4 - α) *
      weightedDensity ((4 - α) / 2) y (energyValue u) x) = derivativeSlice α u y := by
    funext x
    exact (derivativeSlice_split hα2 u y x).symm
  rwa [hf] at hb

/-- Literal translated potential-kernel/coordinate-gradient slice. -/
theorem localGradientSlice_spatialBound (hDensity : OrdinaryH1Density)
    {K α A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A) (j : Fin 3) (y : V) :
    SpatialBound (localGradientSlice α u j y) 1
      (A ^ (4 - α) * localGradientConstant K α (pureGradientNorm u)) := by
  have hb := spatialBound_mul_bounded
    (local_cauchy_spatialBound hDensity hSob hα2 hα3 y u j)
    (value_power_aestronglyMeasurable u (4 - α)) (Real.rpow_nonneg hA0 _)
    (value_power_ae_bound u (by linarith : 0 ≤ 4 - α) hA)
  have hf : (fun x => ‖energyValue u x‖ ^ (4 - α) *
      (weightedDensity (3 - α) y (energyValue u) x ^ (1 / 2 : ℝ) *
        ‖energyGradient j u x‖)) = localGradientSlice α u j y := by
    funext x
    exact (localGradientSlice_split hα2 u j y x).symm
  rwa [hf] at hb

/-- Both domains are on the same original value and hold for every translated center. -/
theorem weighted_slices_integrable_and_bound (hDensity : OrdinaryH1Density)
    {K α A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A) (j : Fin 3) (y : V) :
    (Integrable (derivativeSlice α u y) volume ∧
      (∫ x, derivativeSlice α u y x) ≤
        A ^ (4 - α) * derivativeConstant K α (pureGradientNorm u)) ∧
    (Integrable (localGradientSlice α u j y) volume ∧
      (∫ x, localGradientSlice α u j y x) ≤
        A ^ (4 - α) * localGradientConstant K α (pureGradientNorm u)) := by
  exact ⟨(nonnegative_integral_of_spatialBound_one
      (derivativeSlice_spatialBound hDensity hSob hα2 hα3 hA0 u hA y)
      (derivativeSlice_nonneg α u y)).2,
    (nonnegative_integral_of_spatialBound_one
      (localGradientSlice_spatialBound hDensity hSob hα2 hα3 hA0 u hA j y)
      (localGradientSlice_nonneg α u j y)).2⟩

end HartreeF.WeightedRieszProduct
