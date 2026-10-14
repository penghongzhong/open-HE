import FEnergyRegularizerLaplacian
import FStateDerivativeFromGradient
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped Topology ENNReal
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open FreeFlow (phase phaseMultiply phaseMultiply_coe phase_zero phase_norm phase_temperate l2_norm_sq_integral)

theorem phase_cutoff_hasDerivAt (n : ℕ) (ξ : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phase s ξ * symbol n ξ)
      (Complex.I * phase t ξ * laplaceSymbol n ξ) t := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-Complex.I)).mul_const
    (((2 * Real.pi)^2 * ‖ξ‖^2 : ℝ) : ℂ)).cexp.mul_const (symbol n ξ)
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  convert h using 1 <;> simp only [phase, laplaceSymbol, normSqSymbol, Pi.smul_apply,
    Pi.mul_apply, smul_eq_mul]
  push_cast
  ring

theorem phase_cutoff_slope_bound (n : ℕ) (ξ : V) (h : ℝ) :
    ‖h⁻¹ • ((phase h ξ - 1) * symbol n ξ)‖ ≤ (laplaceCutoff n).bound := by
  by_cases hh : h = 0
  · simp [hh, (laplaceCutoff n).bound_nonneg]
  have hb : ‖phase h ξ * symbol n ξ - phase 0 ξ * symbol n ξ‖ ≤
      (laplaceCutoff n).bound * ‖h‖ := by
    have H := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun t : ℝ => phase t ξ * symbol n ξ)
      (f' := fun t => Complex.I * phase t ξ * laplaceSymbol n ξ)
      (fun t _ => (phase_cutoff_hasDerivAt n ξ t).hasDerivWithinAt)
      (fun t _ => by
        simpa only [norm_mul, Complex.norm_I, phase_norm, one_mul, laplaceCutoff] using
          (laplaceCutoff n).norm_le ξ)
      (Set.mem_univ 0) (Set.mem_univ h)
    simpa only [sub_zero, laplaceCutoff] using H
  rw [norm_smul, norm_inv]
  have hz : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have he : (phase h ξ - 1) * symbol n ξ =
      phase h ξ * symbol n ξ - phase 0 ξ * symbol n ξ := by rw [phase_zero]; ring
  rw [he]
  calc
    ‖h‖⁻¹ * ‖phase h ξ * symbol n ξ - phase 0 ξ * symbol n ξ‖ ≤
        ‖h‖⁻¹ * ((laplaceCutoff n).bound * ‖h‖) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hz.le)
    _ = (laplaceCutoff n).bound := by field_simp


theorem phaseMultiply_zero_native (f : L2) : phaseMultiply 0 f = f := by
  apply Lp.ext
  filter_upwards [phaseMultiply_coe 0 f] with ξ hξ
  simpa only [phase_zero, one_mul] using hξ

/-- Dominated convergence of actual spectral difference quotients. The
majorant uses |xi|^2 m_n, never the mass of the original energy state. -/
theorem phaseMultiply_cutoff_hasDerivAt_zero (n : ℕ) (f : L2) :
    HasDerivAt (fun t : ℝ => phaseMultiply t ((cutoff n).multiply f))
      (Complex.I • (laplaceCutoff n).multiply f) 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simp only [zero_add, phaseMultiply_zero_native]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let r : ℝ → V → ℂ := fun h ξ =>
    h⁻¹ • ((phase h ξ - 1) * symbol n ξ) - Complex.I * laplaceSymbol n ξ
  have hg : Integrable (fun ξ => ‖f ξ‖^2) := (Lp.memLp f).norm.integrable_sq
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[≠] (0 : ℝ)) (F := fun h ξ => ‖r h ξ * f ξ‖^2)
    (f := fun _ => (0 : ℝ)) (fun ξ => (2 * (laplaceCutoff n).bound)^2 * ‖f ξ‖^2)
    (Eventually.of_forall fun h => by
      have hr : Continuous (r h) := by
        dsimp [r]
        exact ((((phase_temperate h).1.continuous.sub continuous_const).mul
          (symbol_temperate n).1.continuous).const_smul h⁻¹).sub
            (continuous_const.mul (laplaceSymbol_temperate n).1.continuous)
      exact (hr.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)).norm.pow 2)
    (Eventually.of_forall fun h => Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hr : ‖r h ξ‖ ≤ 2 * (laplaceCutoff n).bound := by
        calc
          _ ≤ ‖h⁻¹ • ((phase h ξ - 1) * symbol n ξ)‖ +
              ‖Complex.I * laplaceSymbol n ξ‖ := norm_sub_le _ _
          _ ≤ (laplaceCutoff n).bound + (laplaceCutoff n).bound := by
            apply add_le_add (phase_cutoff_slope_bound n ξ h)
            simpa only [norm_mul, Complex.norm_I, one_mul, laplaceCutoff] using (laplaceCutoff n).norm_le ξ
          _ = _ := by ring
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hr 2) (sq_nonneg _))
    (hg.const_mul _) (Eventually.of_forall fun ξ => by
      have hs : Tendsto (fun h : ℝ => h⁻¹ • ((phase h ξ - 1) * symbol n ξ))
          (𝓝[≠] 0) (𝓝 (Complex.I * laplaceSymbol n ξ)) := by
        simpa only [zero_add, phase_zero, mul_one, one_mul, sub_mul] using
          (phase_cutoff_hasDerivAt n ξ 0).tendsto_slope_zero
      have ht := (hs.sub (tendsto_const_nhds (x := Complex.I * laplaceSymbol n ξ))).mul_const (f ξ)
      simpa only [sub_self, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)] using ht.norm.pow 2)
  have hid (h : ℝ) :
      ‖h⁻¹ • (phaseMultiply h ((cutoff n).multiply f) - (cutoff n).multiply f) -
          Complex.I • (laplaceCutoff n).multiply f‖^2 =
        ∫ ξ, ‖r h ξ * f ξ‖^2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
        (h⁻¹ • (phaseMultiply h ((cutoff n).multiply f) - (cutoff n).multiply f))
        (Complex.I • (laplaceCutoff n).multiply f),
      Lp.coeFn_smul h⁻¹ (phaseMultiply h ((cutoff n).multiply f) - (cutoff n).multiply f),
      Lp.coeFn_sub (phaseMultiply h ((cutoff n).multiply f)) ((cutoff n).multiply f),
      Lp.coeFn_smul Complex.I ((laplaceCutoff n).multiply f),
      phaseMultiply_coe h ((cutoff n).multiply f), (cutoff n).multiply_coe f,
      (laplaceCutoff n).multiply_coe f] with ξ h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₃, Pi.sub_apply,
      h₄, Pi.smul_apply, h₅, h₆, h₇]
    congr 2
    change h⁻¹ • (phase h ξ * (symbol n ξ * f ξ) - symbol n ξ * f ξ) -
      Complex.I * (laplaceSymbol n ξ * f ξ) = _
    simp only [r, Algebra.smul_def]
    ring
  have hsq : Tendsto (fun h : ℝ =>
      ‖h⁻¹ • (phaseMultiply h ((cutoff n).multiply f) - (cutoff n).multiply f) -
          Complex.I • (laplaceCutoff n).multiply f‖^2) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hid, integral_zero] using hd
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot


theorem freeL2_cutoff_hasDerivAt_zero (n : ℕ) (f : L2) :
    HasDerivAt (fun t : ℝ => FreeFlow.freeL2 t ((cutoff n).l2 f))
      (Complex.I • (laplaceCutoff n).l2 f) 0 := by
  have h := ((fourierInvCLM ℂ L2).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (phaseMultiply_cutoff_hasDerivAt_zero n (𝓕 f))
  change HasDerivAt (fun t : ℝ => 𝓕⁻ (phaseMultiply t (𝓕 ((cutoff n).l2 f))))
    (Complex.I • 𝓕⁻ ((laplaceCutoff n).multiply (𝓕 f))) 0
  simpa only [BoundedSymbol.l2_fourier, ContinuousLinearMap.coe_restrictScalars',
    Function.comp_def, map_smul, fourierInvCLM_apply] using! h

theorem freeL2_cutoff_hasDerivAt (n : ℕ) (f : L2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => FreeFlow.freeL2 s ((cutoff n).l2 f))
      (Complex.I • FreeFlow.freeL2 t ((laplaceCutoff n).l2 f)) t := by
  have h := ((FreeFlow.freeL2 t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (freeL2_cutoff_hasDerivAt_zero n f)
  have hshift := HasDerivAt.comp_sub_const t t (by simpa only [sub_self] using h)
  simpa only [ContinuousLinearMap.coe_restrictScalars', Function.comp_def,
    ← FreeFlow.freeL2_add, add_sub_cancel, map_smul] using hshift

/-- Native strong derivative on the actual homogeneous energy state. Only
its three existing L2 gradient coordinates enter the Fourier proof. -/
theorem regularized_free_hasDerivAt (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) (t : ℝ) :
    HasDerivAt (fun s : ℝ => freeEnergyState hDensity hSob s (J hDensity hSob n u))
      (Complex.I • freeEnergyState hDensity hSob t (deltaJ hDensity hSob n u)) t := by
  apply hasDerivAt_of_gradient_hasDerivAt hSob
  intro j
  simpa only [map_smul, freeEnergyState_gradient, J_gradient, deltaJ_gradient] using
    freeL2_cutoff_hasDerivAt n (energyGradient j u) t

#print axioms regularized_free_hasDerivAt
#print axioms phaseMultiply_cutoff_hasDerivAt_zero
#print axioms phase_cutoff_hasDerivAt
#print axioms phase_cutoff_slope_bound
end HartreeF.Regularization.Actual
