import HartreeProductBounds
import LocallyDominatedWeakClosure

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeProduct
open ForcingDomain RieszWeakDerivative WeakHartreeChain SobolevStretch StationarySelfTest WeakCutoffLp

def cutoffPotentialProduct (α c : ℝ) (F : ℂ → ℝ) (u : Space → ℂ) (χ : Space → ℝ) : Space → ℝ :=
  fun x => χ x*potentialProduct α c F u x

def cutoffPotentialProductGradient (α c : ℝ) (F : ℂ → ℝ) (u : Space → ℂ)
    (U V : Space → Space) (χ : Space → ℝ) : Space → Space :=
  fun x => χ x • potentialProductGradient α c F u U V x+potentialProduct α c F u x • gradient χ x

def cutoffFunctionMagnitude (α c : ℝ) (u : Space → ℂ) (χ : Space → ℝ) : Space → ℝ :=
  fun x => ‖χ x‖*forcingMagnitude α c u x

def cutoffGradientMagnitude (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) (χ : Space → ℝ) : Space → ℝ :=
  fun x => ‖χ x‖*gradientMagnitude α c u U V x+forcingMagnitude α c u x*‖gradient χ x‖

theorem cutoff_product_bounds {α c : ℝ} {F : ℂ → ℝ}
    (hfb : ∀ z, ‖F z‖ ≤ ‖z‖^(2+α))
    (hdb : ∀ z, ‖fderiv ℝ F z‖ ≤ (3*(2+α))*‖z‖^(1+α))
    (u : Space → ℂ) (U V : Space → Space) (χ : Space → ℝ) (x : Space) :
    ‖cutoffPotentialProduct α c F u χ x‖ ≤ cutoffFunctionMagnitude α c u χ x ∧
    ‖cutoffPotentialProductGradient α c F u U V χ x‖ ≤ cutoffGradientMagnitude α c u U V χ x := by
  constructor
  · rw [cutoffPotentialProduct,norm_mul]
    exact mul_le_mul_of_nonneg_left (potentialProduct_norm_bound hfb u x) (norm_nonneg _)
  · calc
      _ ≤ ‖χ x • potentialProductGradient α c F u U V x‖+‖potentialProduct α c F u x • gradient χ x‖ := norm_add_le _ _
      _ ≤ ‖χ x‖*gradientMagnitude α c u U V x+forcingMagnitude α c u x*‖gradient χ x‖ := by
        rw [norm_smul,norm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_left (potentialProductGradient_norm_bound hfb hdb u U V x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (potentialProduct_norm_bound hfb u x) (norm_nonneg _))
      _ = _ := rfl

theorem cutoff_product_magnitude_domains {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume)
    {χ : Space → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemLp (cutoffFunctionMagnitude α c u χ) (ENNReal.ofReal (6/5 : ℝ)) volume ∧
    MemLp (cutoffGradientMagnitude α c u U V χ) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  have hχTop := (cutoff_memLp hχ.continuous hc ∞).norm
  have hdχTop := (cutoff_gradient_memLp hχ hc ∞).norm
  have hf := forcingMagnitude_memLp hH hu6
  have hg := gradientMagnitude_memLp hH hu6 hu10 hU hV
  exact ⟨hχTop.mul hf,(hχTop.mul hg).add (hf.mul hdχTop)⟩

theorem cutoff_product_domains {α c : ℝ} (hH : OrdinaryHLS α c)
    {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F) (hfb : ∀ z, ‖F z‖ ≤ ‖z‖^(2+α))
    (hdb : ∀ z, ‖fderiv ℝ F z‖ ≤ (3*(2+α))*‖z‖^(1+α))
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume)
    {χ : Space → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemLp (cutoffPotentialProduct α c F u χ) (ENNReal.ofReal (6/5 : ℝ)) volume ∧
    MemLp (cutoffPotentialProductGradient α c F u U V χ) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  have hf := potentialProduct_memLp hH hF.continuous hfb hu6 hu10
  have hg := potentialProductGradient_memLp hH hF hfb hdb hu6 hu10 hU hV
  exact ⟨cutoff_smul_memLp hχ.continuous hc hf,
    (cutoff_smul_memLp hχ.continuous hc hg).add (hf.smul (cutoff_gradient_memLp hχ hc ∞))⟩

theorem retracted_localFactor_growth_bounds {α : ℝ} (hα : 0 < α)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (n : ℕ) :
    let F := retractedMap (projectedLocalFactor (1+α) L) (saturationParameter n)
    (∀ z, ‖F z‖ ≤ ‖z‖^(2+α)) ∧
    (∀ z, ‖fderiv ℝ F z‖ ≤ (3*(2+α))*‖z‖^(1+α)) := by
  dsimp only
  have hq : 1 < 1+α := by linarith
  have he := saturationParameter_pos n
  have hpow : 1+α+1 = 2+α := by ring
  constructor
  · intro z
    have h := retractedMap_norm_bound (by linarith : 0 ≤ 1+α+1) (by norm_num : (0 : ℝ)≤1) he.le
      (projectedLocalFactor_norm_bound hq L hL) z
    simpa only [one_mul,hpow] using h
  · intro z
    have h := retractedMap_fderiv_bound (projectedLocalFactor_contDiff_one hq L) (by linarith : 0 ≤ 1+α)
      (by linarith : 0 ≤ 1+α+1) he.le (projectedLocalFactor_fderiv_bound hq L hL) z
    simpa only [hpow] using h

theorem localFactor_growth_bounds {α : ℝ} (hα : 0 < α)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    (∀ z, ‖projectedLocalFactor (1+α) L z‖ ≤ ‖z‖^(2+α)) ∧
    (∀ z, ‖fderiv ℝ (projectedLocalFactor (1+α) L) z‖ ≤ (3*(2+α))*‖z‖^(1+α)) := by
  have hq : 1 < 1+α := by linarith
  have he : 1+α+1 = 2+α := by ring
  constructor
  · intro z
    simpa only [he,one_mul] using projectedLocalFactor_norm_bound hq L hL z
  · intro z
    have h := projectedLocalFactor_fderiv_bound hq L hL z
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith : 2+α ≤ 3*(2+α)) (Real.rpow_nonneg (norm_nonneg _) _))

theorem cutoff_retracted_product_hasWeakGradient (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume)
    {χ : Space → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (n : ℕ) :
    let F := retractedMap (projectedLocalFactor (1+α) L) (saturationParameter n)
    HasWeakGradient (cutoffPotentialProduct α c F u χ) (cutoffPotentialProductGradient α c F u U V χ) := by
  dsimp only
  have hp := cutoff_potential_domains hH hu.function_L6 hu10 hU hV hχ hc
  have hb := retracted_localFactor_H1_domains hDensity (by linarith [hH.order_pos] : 1 < 1+α) L hL hu n
  have hw := weak_leibniz_L2_L65_H1 hDensity hSob
    ((hartree_potential_hasWeakGradient hDensity hH hu hu10 hU hV).mul_smooth hχ)
    hb.2.2 hp.1 hp.2 hb.1 hb.2.1
  convert hw using 1
  · funext x
    unfold cutoffPotentialProduct potentialProduct
    ring
  · funext x
    unfold cutoffPotentialProductGradient potentialProductGradient potentialProduct
    module

#print axioms cutoff_product_bounds
#print axioms cutoff_product_magnitude_domains
#print axioms cutoff_product_domains
#print axioms retracted_localFactor_growth_bounds
#print axioms localFactor_growth_bounds
#print axioms cutoff_retracted_product_hasWeakGradient
end HartreeF.WeakHartreeProduct
