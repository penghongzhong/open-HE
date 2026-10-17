import FWeightedHardyAlgebra
import FSameStateHardy
import GradientLpBounds

/-! Genuine Holder on the actual Hardy-weighted and L6 values of one EnergyState.
The imported SpatialBound multiplication/power theorems have ordinary proofs;
no HLS interface or weighted-bound conclusion is a premise of this module. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeightedHardy
open EnergySpace SobolevStretch StationarySelfTest SameStateHardy GradientMajorants

theorem weightedDensity_congr_ae {s : ℝ} {y : V} {f g : V → ℂ}
    (h : f =ᵐ[volume] g) : weightedDensity s y f =ᵐ[volume] weightedDensity s y g := by
  filter_upwards [h] with x hx
  simp only [weightedDensity, hx]

theorem hardy_norm_spatialBound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (y : V) (u : EnergyState) :
    SpatialBound (fun x => ‖weightedValue y u x‖) (1 / 2) (2 * pureGradientNorm u) := by
  have hw := energy_hardy_memLp_and_norm hDensity hSob y u
  refine ⟨by norm_num, ?_, ?_⟩
  · simpa only [one_div_div, div_one, ENNReal.ofReal_ofNat] using hw.1.norm
  · change (eLpNorm (fun x => ‖weightedValue y u x‖)
      (ENNReal.ofReal (1 / (1 / 2 : ℝ))) volume).toReal ≤ _
    rw [one_div_div, div_one, ENNReal.ofReal_ofNat,
      eLpNorm_norm _ hw.1.aestronglyMeasurable]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw.2
    simpa only [ENNReal.toReal_ofReal
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (pureGradientNorm_nonneg u))] using h

theorem energy_norm_spatialBound {K : ℝ} (hSob : OrdinarySobolev K) (u : EnergyState) :
    SpatialBound (fun x => ‖energyValue u x‖) (1 / 6)
      (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · simpa only [one_div_div, div_one, ENNReal.ofReal_ofNat] using (Lp.memLp (energyValue u)).norm
  · change (eLpNorm (fun x => ‖energyValue u x‖)
      (ENNReal.ofReal (1 / (1 / 6 : ℝ))) volume).toReal ≤ _
    rw [one_div_div, div_one, ENNReal.ofReal_ofNat,
      eLpNorm_norm _ (Lp.aestronglyMeasurable (energyValue u))]
    exact energyValue_le_pureGradient hSob u

theorem actual_weighted_power_identity {s : ℝ} (hs1 : s < 1) (y : V) (u : EnergyState) :
    (fun x => ‖weightedValue y u x‖ ^ (2 * s) *
      ‖energyValue u x‖ ^ (6 * (1 - s))) = weightedDensity s y (energyValue u) := by
  funext x
  have hn : ‖weightedValue y u x‖ = ‖x - y‖⁻¹ * ‖energyValue u x‖ := by
    rw [weightedValue, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  rw [hn]
  exact scalar_weight_identity (norm_nonneg _) (norm_nonneg _) hs1

/-- The actual weighted function's L1 domain and bound are produced by Holder. -/
theorem weighted_density_spatialBound (hDensity : OrdinaryH1Density) {K s : ℝ}
    (hSob : OrdinarySobolev K) (hs : 0 < s) (hs1 : s < 1) (y : V) (u : EnergyState) :
    SpatialBound (weightedDensity s y (energyValue u)) 1
      (weightedConstant K s (pureGradientNorm u)) := by
  have hw := (hardy_norm_spatialBound hDensity hSob y u).rpow
    (fun x => norm_nonneg (weightedValue y u x)) (by linarith : 0 < 2 * s)
  have hv := (energy_norm_spatialBound hSob u).rpow
    (fun x => norm_nonneg (energyValue u x)) (by linarith : 0 < 6 * (1 - s))
  have hh := hw.mul hv
  have hexp : (2 * s) * (1 / 2) + (6 * (1 - s)) * (1 / 6) = (1 : ℝ) := by ring
  rw [hexp, actual_weighted_power_identity hs1 y u,
    interpolation_constant hSob.nonneg (pureGradientNorm_nonneg u) hs1] at hh
  exact hh

/-- Ordinary L1 norm to integral, with membership and nonnegativity retained. -/
theorem nonnegative_integral_of_spatialBound_one {f : V → ℝ} {B : ℝ}
    (hf : SpatialBound f 1 B) (hn : ∀ x, 0 ≤ f x) :
    MemLp f 1 volume ∧ Integrable f volume ∧ (∫ x, f x) ≤ B := by
  have hm : MemLp f 1 volume := by simpa only [one_div_one, ENNReal.ofReal_one] using hf.memLp
  have hb : (eLpNorm f 1 volume).toReal ≤ B := by
    simpa only [spatialNorm, one_div_one, ENNReal.ofReal_one] using hf.bound
  have heq : (eLpNorm f 1 volume).toReal = ∫ x, f x := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hm]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one]
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => norm_nonneg (f x)))]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).trans (abs_of_nonneg (hn x))
  exact ⟨hm, memLp_one_iff_integrable.mp hm, heq ▸ hb⟩

/-- Same original value, all translated centers, exact Hardy-Sobolev constant. -/
theorem weighted_integral_domain_bound (hDensity : OrdinaryH1Density) {K s : ℝ}
    (hSob : OrdinarySobolev K) (hs : 0 < s) (hs1 : s < 1) (y : V) (u : EnergyState) :
    MemLp (weightedDensity s y (energyValue u)) 1 volume ∧
    Integrable (weightedDensity s y (energyValue u)) volume ∧
    (∫ x, weightedDensity s y (energyValue u) x) ≤
      weightedConstant K s (pureGradientNorm u) :=
  nonnegative_integral_of_spatialBound_one
    (weighted_density_spatialBound hDensity hSob hs hs1 y u)
    (weightedDensity_nonneg s y (energyValue u))

def weightedOne (hDensity : OrdinaryH1Density) {K s : ℝ}
    (hSob : OrdinarySobolev K) (hs : 0 < s) (hs1 : s < 1) (y : V) (u : EnergyState) :
    Lp ℝ 1 (volume : Measure V) :=
  (weighted_integral_domain_bound hDensity hSob hs hs1 y u).1.toLp
    (weightedDensity s y (energyValue u))

theorem weightedOne_coeFn (hDensity : OrdinaryH1Density) {K s : ℝ}
    (hSob : OrdinarySobolev K) (hs : 0 < s) (hs1 : s < 1) (y : V) (u : EnergyState) :
    (weightedOne hDensity hSob hs hs1 y u : V → ℝ) =ᵐ[volume]
      weightedDensity s y (energyValue u) :=
  (weighted_integral_domain_bound hDensity hSob hs hs1 y u).1.coeFn_toLp

theorem weightedOne_norm_le (hDensity : OrdinaryH1Density) {K s : ℝ}
    (hSob : OrdinarySobolev K) (hs : 0 < s) (hs1 : s < 1) (y : V) (u : EnergyState) :
    ‖weightedOne hDensity hSob hs hs1 y u‖ ≤ weightedConstant K s (pureGradientNorm u) := by
  rw [weightedOne, Lp.norm_toLp]
  simpa only [spatialNorm, one_div_one, ENNReal.ofReal_one] using
    (weighted_density_spatialBound hDensity hSob hs hs1 y u).bound

end HartreeF.WeightedHardy
