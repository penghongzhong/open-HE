import FEnergyBanach
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.EnergyRegularizer
open EnergySpace Filter
open scoped Topology ContDiff

def scale (n : ℕ) : ℝ := (n : ℝ) + 1

def resolvent (a : ℝ) (ξ : V) : ℝ := (1 + ‖a • ξ‖ ^ 2)⁻¹

def realSymbol (n : ℕ) (ξ : V) : ℝ :=
  (1 - resolvent (scale n) ξ) * resolvent (scale n)⁻¹ ξ

def symbol (n : ℕ) (ξ : V) : ℂ := realSymbol n ξ

lemma scale_pos (n : ℕ) : 0 < scale n := by unfold scale; positivity
lemma scale_ne_zero (n : ℕ) : scale n ≠ 0 := ne_of_gt (scale_pos n)

lemma resolvent_pos (a : ℝ) (ξ : V) : 0 < resolvent a ξ := by
  unfold resolvent
  positivity

lemma resolvent_le_one (a : ℝ) (ξ : V) : resolvent a ξ ≤ 1 := by
  unfold resolvent
  apply inv_le_one_of_one_le₀
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma resolvent_temperate (a : ℝ) : Function.HasTemperateGrowth (resolvent a) := by
  have h := Function.hasTemperateGrowth_one_add_norm_sq_rpow V (-1)
  have hs : Function.HasTemperateGrowth (fun ξ : V => a • ξ) := by fun_prop
  convert! h.comp hs using 1
  ext ξ
  simp [Real.rpow_neg_one, resolvent]

lemma realSymbol_temperate (n : ℕ) : Function.HasTemperateGrowth (realSymbol n) := by
  exact ((Function.HasTemperateGrowth.const (1 : ℝ)).sub (resolvent_temperate _)).mul
    (resolvent_temperate _)

lemma symbol_temperate (n : ℕ) : Function.HasTemperateGrowth (symbol n) := by
  exact Complex.hasTemperateGrowth_ofReal.comp (realSymbol_temperate n)

lemma realSymbol_nonneg (n : ℕ) (ξ : V) : 0 ≤ realSymbol n ξ := by
  exact mul_nonneg (sub_nonneg.mpr (resolvent_le_one _ _)) (le_of_lt (resolvent_pos _ _))

lemma realSymbol_le_one (n : ℕ) (ξ : V) : realSymbol n ξ ≤ 1 := by
  calc
    _ ≤ 1 * resolvent (scale n)⁻¹ ξ := mul_le_mul_of_nonneg_right (by linarith [resolvent_pos (scale n) ξ]) (le_of_lt (resolvent_pos _ _))
    _ ≤ 1 := by simpa using resolvent_le_one (scale n)⁻¹ ξ

lemma symbol_norm_le_one (n : ℕ) (ξ : V) : ‖symbol n ξ‖ ≤ 1 := by
  simpa [symbol, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (realSymbol_nonneg n ξ)]
    using realSymbol_le_one n ξ

@[simp] lemma symbol_zero (n : ℕ) : symbol n 0 = 0 := by simp [symbol, realSymbol, resolvent]
@[simp] lemma star_symbol (n : ℕ) (ξ : V) : star (symbol n ξ) = symbol n ξ := by simp [symbol]

lemma resolvent_eq (a : ℝ) (ξ : V) : resolvent a ξ = (1 + a ^ 2 * ‖ξ‖ ^ 2)⁻¹ := by
  simp [resolvent, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma scale_tendsto : Tendsto scale atTop atTop := by
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

lemma resolvent_large_tendsto (ξ : V) (hξ : ξ ≠ 0) :
    Tendsto (fun n => resolvent (scale n) ξ) atTop (𝓝 0) := by
  simp_rw [resolvent_eq]
  apply Filter.Tendsto.inv_tendsto_atTop
  have hp : 0 < ‖ξ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hξ) 2
  exact tendsto_atTop_add_const_left _ 1
    (((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp scale_tendsto).atTop_mul_const hp)

lemma resolvent_small_tendsto (ξ : V) :
    Tendsto (fun n => resolvent (scale n)⁻¹ ξ) atTop (𝓝 1) := by
  simp_rw [resolvent_eq]
  have h := ((scale_tendsto.inv_tendsto_atTop.pow 2).mul_const (‖ξ‖ ^ 2)).const_add 1
  simpa using h.inv₀ (by norm_num : (1 + 0 ^ 2 * ‖ξ‖ ^ 2 : ℝ) ≠ 0)

lemma realSymbol_tendsto (ξ : V) (hξ : ξ ≠ 0) :
    Tendsto (fun n => realSymbol n ξ) atTop (𝓝 1) := by
  simpa [realSymbol] using (tendsto_const_nhds.sub (resolvent_large_tendsto ξ hξ)).mul
    (resolvent_small_tendsto ξ)

lemma symbol_tendsto (ξ : V) (hξ : ξ ≠ 0) :
    Tendsto (fun n => symbol n ξ) atTop (𝓝 1) := by
  exact_mod_cast (Complex.continuous_ofReal.tendsto 1).comp (realSymbol_tendsto ξ hξ)

lemma norm_mul_resolvent_inv_le (a : ℝ) (ha : 0 < a) (ξ : V) :
    ‖ξ‖ * resolvent a⁻¹ ξ ≤ a := by
  rw [resolvent_eq]
  have hd : 0 < 1 + a⁻¹ ^ 2 * ‖ξ‖ ^ 2 := by positivity
  apply (mul_inv_le_iff₀ hd).mpr
  have ha0 : a ≠ 0 := ne_of_gt ha
  apply (mul_le_mul_iff_left₀ ha).mp
  field_simp
  nlinarith [sq_nonneg (a - ‖ξ‖)]

lemma symbol_weighted_norm_le (n : ℕ) (ξ : V) :
    ‖ξ‖ * ‖symbol n ξ‖ ≤ scale n := by
  have hr : ‖symbol n ξ‖ = realSymbol n ξ := by
    simp [symbol, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (realSymbol_nonneg n ξ)]
  rw [hr, realSymbol]
  calc
    _ ≤ ‖ξ‖ * (1 * resolvent (scale n)⁻¹ ξ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith [resolvent_pos (scale n) ξ])
          (le_of_lt (resolvent_pos _ _))) (norm_nonneg _)
    _ ≤ scale n := by simpa using norm_mul_resolvent_inv_le (scale n) (scale_pos n) ξ

lemma norm_sq_mul_resolvent_inv_le (a : ℝ) (ha : 0 < a) (ξ : V) :
    ‖ξ‖ ^ 2 * resolvent a⁻¹ ξ ≤ a ^ 2 := by
  rw [resolvent_eq]
  have hd : 0 < 1 + a⁻¹ ^ 2 * ‖ξ‖ ^ 2 := by positivity
  apply (mul_inv_le_iff₀ hd).mpr
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp
  nlinarith [sq_nonneg a]

lemma symbol_sq_weighted_norm_le (n : ℕ) (ξ : V) :
    ‖ξ‖ ^ 2 * ‖symbol n ξ‖ ≤ scale n ^ 2 := by
  have hr : ‖symbol n ξ‖ = realSymbol n ξ := by
    simp [symbol, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (realSymbol_nonneg n ξ)]
  rw [hr, realSymbol]
  calc
    _ ≤ ‖ξ‖ ^ 2 * (1 * resolvent (scale n)⁻¹ ξ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (by linarith [resolvent_pos (scale n) ξ])
          (le_of_lt (resolvent_pos _ _))) (sq_nonneg _)
    _ ≤ scale n ^ 2 := by simpa using norm_sq_mul_resolvent_inv_le (scale n) (scale_pos n) ξ

def realReconstruction (n : ℕ) (j : Fin 3) (ξ : V) : ℝ :=
  scale n ^ 2 * ξ j * resolvent (scale n) ξ * resolvent (scale n)⁻¹ ξ

def reconstruction (n : ℕ) (j : Fin 3) (ξ : V) : ℂ :=
  (-(Complex.I) / (2 * Real.pi)) * realReconstruction n j ξ

def derivativeSymbol (j : Fin 3) (ξ : V) : ℂ :=
  (2 * Real.pi * Complex.I) * (ξ j : ℂ)

lemma realReconstruction_temperate (n : ℕ) (j : Fin 3) :
    Function.HasTemperateGrowth (realReconstruction n j) := by
  have hj : Function.HasTemperateGrowth (fun ξ : V => ξ j) :=
    (EuclideanSpace.proj j).hasTemperateGrowth
  exact (((Function.HasTemperateGrowth.const (scale n ^ 2)).mul hj).mul
    (resolvent_temperate _)).mul (resolvent_temperate _)

lemma reconstruction_temperate (n : ℕ) (j : Fin 3) :
    Function.HasTemperateGrowth (reconstruction n j) := by
  exact (Function.HasTemperateGrowth.const _).mul
    (Complex.hasTemperateGrowth_ofReal.comp (realReconstruction_temperate n j))

lemma realReconstruction_sum (n : ℕ) (ξ : V) :
    ∑ j, realReconstruction n j ξ * ξ j = realSymbol n ξ := by
  have hd : (1 + scale n ^ 2 * ‖ξ‖ ^ 2) ≠ 0 := by positivity
  simp only [realReconstruction, realSymbol]
  calc
    _ = scale n ^ 2 * (∑ j : Fin 3, (ξ j)^2) *
        resolvent (scale n) ξ * resolvent (scale n)⁻¹ ξ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [← EuclideanSpace.real_norm_sq_eq, resolvent_eq (scale n)]
      field_simp
      ring

lemma reconstruction_sum (n : ℕ) (ξ : V) :
    ∑ j, reconstruction n j ξ * derivativeSymbol j ξ = symbol n ξ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hterm (j : Fin 3) : reconstruction n j ξ * derivativeSymbol j ξ =
      (realReconstruction n j ξ * ξ j : ℝ) := by
    simp only [reconstruction, derivativeSymbol, Complex.ofReal_mul]
    field_simp
    ring_nf
    simp
  simp_rw [hterm]
  rw [← Complex.ofReal_sum, realReconstruction_sum]
  rfl

lemma realReconstruction_norm_le (n : ℕ) (j : Fin 3) (ξ : V) :
    ‖realReconstruction n j ξ‖ ≤ scale n := by
  have ha : 0 < scale n := scale_pos n
  have hL : 0 ≤ resolvent (scale n) ξ := le_of_lt (resolvent_pos _ _)
  have hS : 0 ≤ resolvent (scale n)⁻¹ ξ := le_of_lt (resolvent_pos _ _)
  have hweighted : ‖ξ‖ * resolvent (scale n) ξ ≤ (scale n)⁻¹ := by
    simpa using norm_mul_resolvent_inv_le (scale n)⁻¹ (inv_pos.mpr ha) ξ
  calc
    ‖realReconstruction n j ξ‖ =
        scale n ^ 2 * ‖ξ j‖ * resolvent (scale n) ξ * resolvent (scale n)⁻¹ ξ := by
      simp [realReconstruction, norm_mul, Real.norm_of_nonneg hL,
        Real.norm_of_nonneg hS, Real.norm_of_nonneg (le_of_lt ha)]
    _ ≤ scale n ^ 2 * ‖ξ‖ * resolvent (scale n) ξ * 1 := by
      gcongr
      · exact PiLp.norm_apply_le ξ j
      · exact resolvent_le_one _ _
    _ = scale n ^ 2 * (‖ξ‖ * resolvent (scale n) ξ) := by ring
    _ ≤ scale n ^ 2 * (scale n)⁻¹ :=
      mul_le_mul_of_nonneg_left hweighted (sq_nonneg _)
    _ = scale n := by field_simp

lemma reconstruction_norm_le (n : ℕ) (j : Fin 3) (ξ : V) :
    ‖reconstruction n j ξ‖ ≤ scale n / (2 * Real.pi) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  calc
    ‖reconstruction n j ξ‖ = ‖realReconstruction n j ξ‖ / (2 * Real.pi) := by
      simp [reconstruction, Complex.norm_real,
        Real.norm_of_nonneg (le_of_lt Real.pi_pos), div_eq_mul_inv, mul_comm]
    _ ≤ scale n / (2 * Real.pi) :=
      div_le_div_of_nonneg_right (realReconstruction_norm_le n j ξ) (le_of_lt hπ)

lemma derivativeSymbol_eq_coordinate (j : Fin 3) (ξ : V) :
    derivativeSymbol j ξ = (2 * Real.pi * Complex.I) *
      (inner ℝ ξ (EnergySpace.coordinate j) : ℝ) := by
  simp [derivativeSymbol, EnergySpace.coordinate, EuclideanSpace.inner_single_right]

@[simp] lemma symbol_neg (n : ℕ) (ξ : V) : symbol n (-ξ) = symbol n ξ := by
  simp [symbol, realSymbol, resolvent]

@[simp] lemma realSymbol_zero (n : ℕ) : realSymbol n 0 = 0 := by
  simp [realSymbol, resolvent]

lemma realSymbol_contDiff (n : ℕ) : ContDiff ℝ ∞ (realSymbol n) :=
  (realSymbol_temperate n).1

lemma symbol_contDiff (n : ℕ) : ContDiff ℝ ∞ (symbol n) :=
  (symbol_temperate n).1

lemma reconstruction_contDiff (n : ℕ) (j : Fin 3) : ContDiff ℝ ∞ (reconstruction n j) :=
  (reconstruction_temperate n j).1

#print axioms symbol_temperate
#print axioms symbol_tendsto
#print axioms reconstruction_sum
#print axioms symbol_weighted_norm_le
#print axioms symbol_sq_weighted_norm_le
#print axioms reconstruction_norm_le
end HartreeF.EnergyRegularizer
