import FActualCutoffH1Localization
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalChargeBridge
open EnergySpace

/-- A genuine quadratic chain rule with only a derivative in the bounded dual image.
The weak-PDE producer for this ordinary derivative premise is a separate obligation. -/
theorem symmetric_quadratic_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E →L[ℝ] (E →L[ℝ] ℝ)) (hJ : ∀ v w, J v w = J w v)
    {u : ℝ → E} {t : ℝ} {g : E →L[ℝ] ℝ}
    (hu : ContinuousAt u t) (hd : HasDerivAt (fun s => J (u s)) g t) :
    HasDerivAt (fun s => J (u s) (u s)) (2 * g (u t)) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hv : Tendsto (fun s => u s + u t) (𝓝[≠] t) (𝓝 (u t + u t)) :=
    (hu.tendsto.mono_left nhdsWithin_le_nhds).add tendsto_const_nhds
  have hEval : Continuous (fun z : (E →L[ℝ] ℝ) × E => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hh := (hEval.tendsto (g, u t + u t)).comp (hd.tendsto_slope.prodMk_nhds hv)
  have he (s : ℝ) : slope (fun s => J (u s) (u s)) t s =
      (slope (fun s => J (u s)) t s) (u s + u t) := by
    simp only [slope_def_module, smul_eq_mul, smul_apply,
      sub_apply, map_add]
    rw [hJ (u t) (u s)]
    ring
  simpa only [Function.comp_def, ← he, map_add, ← two_mul] using hh

/-- The actual local L2 quadratic form of chi*u, represented on the original EnergyState. -/
def localizedChargeForm {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) : EnergyState →L[ℝ] (EnergyState →L[ℝ] ℝ) :=
  (innerSL ℝ).bilinearComp ((localizedValue hχ hc).restrictScalars ℝ)
    ((localizedValue hχ hc).restrictScalars ℝ)

theorem localizedChargeForm_symmetric {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (u v : EnergyState) :
    localizedChargeForm hχ hc u v = localizedChargeForm hχ hc v u := by
  change inner ℝ (localizedValue hχ hc u) (localizedValue hχ hc v) =
    inner ℝ (localizedValue hχ hc v) (localizedValue hχ hc u)
  exact real_inner_comm _ _

theorem localizedChargeForm_diagonal {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (u : EnergyState) :
    localizedChargeForm hχ hc u u = ‖localizedValue hχ hc u‖^2 := by
  change inner ℝ (localizedValue hχ hc u) (localizedValue hχ hc u) = _
  exact real_inner_self_eq_norm_sq _

/-- Literal spatial integral, finite even though the original value need not be L2. -/
theorem localized_square_charge_integral {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (u : EnergyState) :
    Integrable (fun x : V => χ x ^ 2 * ‖energyValue u x‖^2) volume ∧
    (∫ x : V, χ x ^ 2 * ‖energyValue u x‖^2) = localizedChargeForm hχ hc u u := by
  have h2 := (energyState_inDotH1 u).cutoff_memLp_two hχ hc
  have he (x : V) : ‖χ x • energyValue u x‖^2 = χ x^2 * ‖energyValue u x‖^2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hint := h2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  simp_rw [he] at hint
  refine ⟨hint, ?_⟩
  rw [localizedChargeForm_diagonal]
  have hnorm := ComplexIMS.integral_norm_sq_eq_eLpNorm_sq (Lp.memLp (localizedValue hχ hc u))
  rw [← Lp.norm_def] at hnorm
  rw [← hnorm]
  apply integral_congr_ae
  filter_upwards [localizedValue_ae hχ hc u] with x hx
  rw [hx, he]

/-- An actual-integral quadratic rule; dual-image differentiability remains explicit. -/
theorem localized_square_charge_hasDerivAt {χ : V → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    {u : ℝ → EnergyState} {t : ℝ} {g : EnergyState →L[ℝ] ℝ}
    (hu : ContinuousAt u t)
    (hd : HasDerivAt (fun s => localizedChargeForm hχ hc (u s)) g t) :
    HasDerivAt (fun s => ∫ x : V, χ x^2 * ‖energyValue (u s) x‖^2) (2 * g (u t)) t := by
  simp_rw [(localized_square_charge_integral hχ hc _).2]
  exact symmetric_quadratic_hasDerivAt _ (localizedChargeForm_symmetric hχ hc) hu hd

/-- Square-root localization realizes the exact accepted chi_R charge. No smoothness of sqrt
is asserted or needed here; the smooth multiplier for the PDE is chi_R itself. -/
def physicalChargeValue {R : ℝ} (hR : 0 < R) : EnergyState →L[ℂ] L2 :=
  (cutoffL6L2 (Real.continuous_sqrt.comp (LocalChargeRigidity.chargeCutoff_smooth R).continuous)
    ((LocalChargeRigidity.chargeCutoff_compact hR).comp_left Real.sqrt_zero)).comp energyValue

def physicalChargeForm {R : ℝ} (hR : 0 < R) : EnergyState →L[ℝ] (EnergyState →L[ℝ] ℝ) :=
  (innerSL ℝ).bilinearComp ((physicalChargeValue hR).restrictScalars ℝ)
    ((physicalChargeValue hR).restrictScalars ℝ)

theorem physicalChargeForm_symmetric {R : ℝ} (hR : 0 < R) (u v : EnergyState) :
    physicalChargeForm hR u v = physicalChargeForm hR v u := by
  change inner ℝ (physicalChargeValue hR u) (physicalChargeValue hR v) =
    inner ℝ (physicalChargeValue hR v) (physicalChargeValue hR u)
  exact real_inner_comm _ _

/-- The same chi(x/R) spatialCharge as in the accepted flux consumer, now finite from L6 alone. -/
theorem original_spatialCharge_form {R : ℝ} (hR : 0 < R) (u : EnergyState) :
    Integrable (fun x : V => LocalChargeRigidity.chargeCutoff R x * ‖energyValue u x‖^2) volume ∧
    LocalChargeRigidity.spatialCharge R (energyValue u) = physicalChargeForm hR u u := by
  have hae := cutoffL6L2_ae
    (Real.continuous_sqrt.comp (LocalChargeRigidity.chargeCutoff_smooth R).continuous)
    ((LocalChargeRigidity.chargeCutoff_compact hR).comp_left Real.sqrt_zero) (energyValue u)
  have he : (fun x : V => ‖physicalChargeValue hR u x‖^2) =ᵐ[volume]
      fun x => LocalChargeRigidity.chargeCutoff R x * ‖energyValue u x‖^2 := by
    filter_upwards [hae] with x hx
    change physicalChargeValue hR u x = _ at hx
    rw [hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Function.comp_apply,
      Real.sq_sqrt (LocalChargeRigidity.chargeCutoff_nonneg R x)]
  refine ⟨((Lp.memLp (physicalChargeValue hR u)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)).congr he, ?_⟩
  change (∫ x : V, LocalChargeRigidity.chargeCutoff R x * ‖energyValue u x‖^2) =
    inner ℝ (physicalChargeValue hR u) (physicalChargeValue hR u)
  rw [real_inner_self_eq_norm_sq, ← integral_congr_ae he,
    ComplexIMS.integral_norm_sq_eq_eLpNorm_sq (Lp.memLp (physicalChargeValue hR u)), ← Lp.norm_def]

/-- Generic dual derivative input produces a derivative of the exact original spatial integral.
No claim is made that the actual Hartree weak PDE already supplies this derivative input. -/
theorem original_spatialCharge_hasDerivAt {R : ℝ} (hR : 0 < R)
    {u : ℝ → EnergyState} {t : ℝ} {g : EnergyState →L[ℝ] ℝ}
    (hu : ContinuousAt u t)
    (hd : HasDerivAt (fun s => physicalChargeForm hR (u s)) g t) :
    HasDerivAt (fun s => LocalChargeRigidity.spatialCharge R (energyValue (u s)))
      (2 * g (u t)) t := by
  simp_rw [(original_spatialCharge_form hR _).2]
  exact symmetric_quadratic_hasDerivAt _ (physicalChargeForm_symmetric hR) hu hd

end HartreeF.LocalChargeBridge
