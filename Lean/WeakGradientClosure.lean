import ActualPairingContinuity
import WeakCutoffLpDomains
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
Strong-L2 closure of the literal compact-C-infinity-test weak gradient.
No chain rule, modulus gradient, or integration-by-parts conclusion is assumed.
All tested products have genuine L1 domains, produced from the L2 domains.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ModulusGradient
open SobolevStretch StationaryPairing

/-- Both sides of every smooth compact test are genuine L1 functions. -/
theorem l2_weak_test_domains {u : Space → ℝ} {V : Space → Space}
    (hu : MemLp u 2 volume) (hV : MemLp V 2 volume)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (v : Space) :
    Integrable (fun x => u x * fderiv ℝ φ x v) volume ∧
    Integrable (fun x => ⟪V x, v⟫ * φ x) volume :=
  weak_test_integrable (hu.locallyIntegrable (by norm_num))
    (hV.locallyIntegrable (by norm_num)) hφ hc v

/-- Closure in the actual function and gradient L2 seminorms. -/
theorem hasWeakGradient_of_strong_l2_limit
    {u : Space → ℝ} {V : Space → Space}
    {un : ℕ → Space → ℝ} {Vn : ℕ → Space → Space}
    (hu : MemLp u 2 volume) (hV : MemLp V 2 volume)
    (hun : ∀ n, MemLp (un n) 2 volume)
    (hVn : ∀ n, MemLp (Vn n) 2 volume)
    (hweak : ∀ n, HasWeakGradient (un n) (Vn n))
    (huconv : Tendsto (fun n => eLpNorm (un n - u) 2 volume) atTop (𝓝 0))
    (hVconv : Tendsto (fun n => eLpNorm (Vn n - V) 2 volume) atTop (𝓝 0)) :
    HasWeakGradient u V := by
  refine ⟨hu.locallyIntegrable (by norm_num), hV.locallyIntegrable (by norm_num), ?_⟩
  intro v φ hφ hc
  have hd : MemLp (fun x => fderiv ℝ φ x v) 2 volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have htest : MemLp (fun x => φ x • v) 2 volume :=
    (hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport
      (hc.smul_right)
  have hl := integral_mul_tendsto_of_eLpNorm hd hu hun huconv
  have hr := integral_inner_tendsto_of_eLpNorm htest hV hVn hVconv
  have hl' : Tendsto (fun n => ∫ x, un n x * fderiv ℝ φ x v) atTop
      (𝓝 (∫ x, u x * fderiv ℝ φ x v)) := by
    simpa only [mul_comm] using hl
  have hr' : Tendsto (fun n => -(∫ x, ⟪Vn n x, v⟫ * φ x)) atTop
      (𝓝 (-(∫ x, ⟪V x, v⟫ * φ x))) := by
    simpa only [real_inner_smul_left, real_inner_comm v, mul_comm] using hr.neg
  apply tendsto_nhds_unique hl'
  convert hr' using 1
  funext n
  exact (hweak n).integration_by_parts v φ hφ hc

/-- Strong L2 convergence supplies an actual almost-everywhere subsequence,
without requiring finite total volume. -/
theorem exists_ae_subsequence_of_strong_l2
    {E : Type*} [NormedAddCommGroup E]
    {u : Space → E} {un : ℕ → Space → E}
    (hconv : Tendsto (fun n => eLpNorm (un n - u) 2 volume) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂volume, Tendsto (fun n => un (ns n) x) atTop (𝓝 (u x)) := by
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    hconv).exists_seq_tendsto_ae

#print axioms l2_weak_test_domains
#print axioms hasWeakGradient_of_strong_l2_limit
#print axioms exists_ae_subsequence_of_strong_l2
end HartreeF.ModulusGradient
