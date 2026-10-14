import FActualSpatialChargeLimit
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.LocalChargeBridge
open EnergySpace EnergySpace.Highpass WeakCutoffLp

local instance fact_three : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

local instance holder_three_six_two : ENNReal.HolderTriple 3 6 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  rw [ENNReal.toReal_add (by simp) (by simp)]
  norm_num⟩

/-- The actual complex Lp class of a compact real coefficient. -/
def coefficientLp {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (p : ℝ≥0∞) : Lp ℂ p (volume : Measure V) :=
  ((cutoff_memLp hχ hc p).continuousLinearMap_comp Complex.ofRealCLM).toLp
    (fun x => (χ x : ℂ))

theorem coefficientLp_ae {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (p : ℝ≥0∞) : (coefficientLp hχ hc p : V → ℂ) =ᵐ[volume] fun x => (χ x : ℂ) :=
  MemLp.coeFn_toLp _

/-- Genuine Holder multiplication L6 to L2; no original L2 assumption. -/
def cutoffL6L2 {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) : L6 →L[ℂ] L2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume 3 6 2 (coefficientLp hχ hc 3)

/-- Genuine bounded multiplication L2 to L2. -/
def cutoffL2L2 {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) : L2 →L[ℂ] L2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 (coefficientLp hχ hc ∞)

theorem cutoffL6L2_ae {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (f : L6) : (cutoffL6L2 hχ hc f : V → ℂ) =ᵐ[volume] fun x => χ x • f x := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := 2) (coefficientLp hχ hc 3) f, coefficientLp_ae hχ hc 3] with x hx hcχ
  simpa only [cutoffL6L2, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hcχ, Complex.real_smul] using hx

theorem cutoffL2L2_ae {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (f : L2) : (cutoffL2L2 hχ hc f : V → ℂ) =ᵐ[volume] fun x => χ x • f x := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (r := 2) (coefficientLp hχ hc ∞) f, coefficientLp_ae hχ hc ∞] with x hx hcχ
  simpa only [cutoffL2L2, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hcχ, Complex.real_smul] using hx

theorem cutoffL6L2_norm {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (f : L6) : ‖cutoffL6L2 hχ hc f‖ ≤ ‖coefficientLp hχ hc 3‖ * ‖f‖ := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le
    (r := 2) (coefficientLp hχ hc 3) f
  exact h.trans (by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.opNorm_mul_le (𝕜 := ℂ) (R := ℂ)) (norm_nonneg _))

theorem cutoffL2L2_norm {χ : V → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (f : L2) : ‖cutoffL2L2 hχ hc f‖ ≤ ‖coefficientLp hχ hc ∞‖ * ‖f‖ := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).norm_holder_apply_apply_le
    (r := 2) (coefficientLp hχ hc ∞) f
  exact h.trans (by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.opNorm_mul_le (𝕜 := ℂ) (R := ℂ)) (norm_nonneg _))

/-- Exact directional derivative of the real coefficient. -/
def coefficientDerivative (χ : V → ℝ) (j : Fin 3) (x : V) : ℝ := fderiv ℝ χ x (coordinate j)

theorem coefficientDerivative_continuous {χ : V → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (j : Fin 3) : Continuous (coefficientDerivative χ j) :=
  (hχ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem coefficientDerivative_compact {χ : V → ℝ}
    (hc : HasCompactSupport χ) (j : Fin 3) : HasCompactSupport (coefficientDerivative χ j) :=
  (hc.fderiv ℝ).comp_left (g := fun A : V →L[ℝ] ℝ => A (coordinate j)) (by simp)

end HartreeF.LocalChargeBridge
