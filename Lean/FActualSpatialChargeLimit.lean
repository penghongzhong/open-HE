import FConditionalActualMassContinuity
import CutoffGeometry
import UniformIMSEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped ENNReal Topology
namespace HartreeF.LocalChargeRigidity
open EnergySpace CutoffApproximation

/-- The genuine physical-space cutoff chi(x/R), not a frequency projector. -/
def chargeCutoff (R : ℝ) (x : V) : ℝ := baseBump (R⁻¹ • x)

theorem chargeCutoff_smooth (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chargeCutoff R) :=
  baseBump.contDiff.comp (contDiff_id.const_smul R⁻¹)

theorem chargeCutoff_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (chargeCutoff R) := by
  let e : V ≃ₜ V := Homeomorph.smul (Units.mk0 R⁻¹ (inv_ne_zero hR.ne'))
  exact baseBump.hasCompactSupport.comp_homeomorph e

theorem chargeCutoff_nonneg (R : ℝ) (x : V) : 0 ≤ chargeCutoff R x := baseBump.nonneg

theorem chargeCutoff_le_one (R : ℝ) (x : V) : chargeCutoff R x ≤ 1 := baseBump.le_one

theorem chargeCutoff_eq_one {R : ℝ} (hR : 0 < R) (x : V) (hx : ‖x‖ ≤ R) :
    chargeCutoff R x = 1 := by
  apply baseBump.one_of_mem_closedBall
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  change R⁻¹ * ‖x‖ ≤ 1
  exact (inv_mul_le_iff₀ hR).mpr (by simpa using hx)

theorem chargeCutoff_eventually_one (x : V) : ∀ᶠ R : ℝ in atTop, chargeCutoff R x = 1 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ‖x‖] with R hR hx
  exact chargeCutoff_eq_one hR x hx

theorem exists_baseGradientBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V,
    ‖gradient (baseBump : V → ℝ) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (WeakCutoffLp.cutoff_gradient_continuous baseBump.contDiff).bounded_above_of_compact_support
    (WeakCutoffLp.cutoff_gradient_hasCompactSupport baseBump.hasCompactSupport)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- A finite constant constructed from the gradient of this exact fixed bump. -/
def baseGradientBound : ℝ := exists_baseGradientBound.choose

theorem baseGradientBound_nonneg : 0 ≤ baseGradientBound := exists_baseGradientBound.choose_spec.1

theorem baseGradientBound_spec (x : V) : ‖gradient (baseBump : V → ℝ) x‖ ≤ baseGradientBound :=
  exists_baseGradientBound.choose_spec.2 x

theorem chargeCutoff_gradient_bound {R : ℝ} (hR : 0 < R) (x : V) :
    ‖gradient (chargeCutoff R) x‖ ≤ baseGradientBound / R := by
  have hd : gradient (chargeCutoff R) x = R⁻¹ • gradient (baseBump : V → ℝ) (R⁻¹ • x) :=
    gradient_comp_smul ((baseBump.contDiff : ContDiff ℝ (⊤ : ℕ∞) (baseBump : V → ℝ)).differentiable (by simp)) R⁻¹ x
  rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (baseGradientBound_spec (R⁻¹ • x)) (inv_nonneg.mpr hR.le)

/-- The literal localized charge integral of an actual spatial function. -/
def spatialCharge (R : ℝ) (f : V → ℂ) : ℝ := ∫ x : V, chargeCutoff R x * ‖f x‖^2

theorem spatialCharge_integrable (R : ℝ) {f : V → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun x : V => chargeCutoff R x * ‖f x‖^2) volume := by
  apply (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mono'
    ((chargeCutoff_smooth R).continuous.aestronglyMeasurable.mul (hf.aestronglyMeasurable.norm.pow 2))
  filter_upwards [] with x
  change ‖chargeCutoff R x * ‖f x‖^2‖ ≤ ‖f x‖^2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (chargeCutoff_nonneg R x) (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) (chargeCutoff_le_one R x)

theorem spatialCharge_congr_ae (R : ℝ) {f g : V → ℂ} (h : f =ᵐ[volume] g) :
    spatialCharge R f = spatialCharge R g := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- Dominated convergence passes the genuine physical cutoff integral to the full mass,
along all real radii R to infinity. -/
theorem spatialCharge_tendsto_mass {f : V → ℂ} (hf : MemLp f 2 volume) :
    Tendsto (fun R : ℝ => spatialCharge R f) atTop (𝓝 (∫ x : V, ‖f x‖^2)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x : V => ‖f x‖^2)
  · exact Eventually.of_forall (fun R => (spatialCharge_integrable R hf).aestronglyMeasurable)
  · filter_upwards [] with R
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (chargeCutoff_nonneg R x) (sq_nonneg _))]
    exact mul_le_of_le_one_left (sq_nonneg _) (chargeCutoff_le_one R x)
  · exact hf.integrable_norm_pow (by norm_num)
  · filter_upwards [] with x
    apply tendsto_const_nhds.congr'
    filter_upwards [chargeCutoff_eventually_one x] with R hR
    simp only [hR, one_mul]

theorem spatialCharge_tendsto_L2_norm (v : L2) :
    Tendsto (fun R : ℝ => spatialCharge R (v : V → ℂ)) atTop (𝓝 (‖v‖^2)) := by
  have h := spatialCharge_tendsto_mass (Lp.memLp v)
  rw [ComplexIMS.integral_norm_sq_eq_eLpNorm_sq (Lp.memLp v), ← Lp.norm_def] at h
  exact h

end HartreeF.LocalChargeRigidity
