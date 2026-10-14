import FFreeFlowCore
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-! Strong continuity proved for the actual Fourier multiplier by dominated
convergence. No linear evolution interface or nonlinear hypothesis is used. -/
namespace HartreeF.FreeFlow
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter
open scoped Topology SchwartzMap

theorem l2_norm_sq_integral (h : L2) : ‖h‖ ^ 2 = ∫ y, ‖h y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem phase_time_continuous (ξ : V) : Continuous (fun t : ℝ => phase t ξ) := by
  unfold phase
  fun_prop

theorem freeL2_fourier (t : ℝ) (f : L2) : 𝓕 (freeL2 t f) = phaseMultiply t (𝓕 f) := by
  change 𝓕 (𝓕⁻ (phaseMultiply t (𝓕 f))) = _
  exact fourier_fourierInv_eq _

theorem freeL2_time_continuous (f : L2) : Continuous (fun t : ℝ => freeL2 t f) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let g : L2 := 𝓕 f
  have hg : Integrable (fun ξ => ‖g ξ‖ ^ 2) := (Lp.memLp g).norm.integrable_sq
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 a) (F := fun t ξ => ‖(phase t ξ - phase a ξ) * g ξ‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun ξ => 4 * ‖g ξ‖ ^ 2)
    (Eventually.of_forall fun t =>
      (((phase_temperate t).1.continuous.aestronglyMeasurable.sub
        (phase_temperate a).1.continuous.aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable g)).norm.pow 2)
    (Eventually.of_forall fun t => Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),norm_mul,mul_pow]
      have hphase : ‖phase t ξ - phase a ξ‖ ≤ 2 := by
        simpa only [phase_norm,one_add_one_eq_two] using norm_sub_le (phase t ξ) (phase a ξ)
      have hs : ‖phase t ξ - phase a ξ‖ ^ 2 ≤ (2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hphase 2
      nlinarith [sq_nonneg ‖g ξ‖])
    (hg.const_mul 4) (Eventually.of_forall fun ξ => by
      have ht := (((phase_time_continuous ξ).tendsto a).sub
        (tendsto_const_nhds (x := phase a ξ))).mul_const (g ξ)
      simpa only [sub_self,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0)] using ht.norm.pow 2)
  have hid (t : ℝ) : ‖freeL2 t f - freeL2 a f‖ ^ 2 =
      ∫ ξ, ‖(phase t ξ - phase a ξ) * g ξ‖ ^ 2 := by
    rw [← Lp.norm_fourier_eq (freeL2 t f - freeL2 a f)]
    have hsub : 𝓕 (freeL2 t f - freeL2 a f) = 𝓕 (freeL2 t f) - 𝓕 (freeL2 a f) :=
      (fourierCLM ℂ L2).map_sub _ _
    rw [hsub,freeL2_fourier,freeL2_fourier,l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (phaseMultiply t g) (phaseMultiply a g),
      phaseMultiply_coe t g,phaseMultiply_coe a g] with ξ hsub ht ha
    rw [hsub,Pi.sub_apply,ht,ha,← sub_mul]
  have hsq : Tendsto (fun t => ‖freeL2 t f - freeL2 a f‖ ^ 2) (𝓝 a) (𝓝 0) := by
    simpa only [hid,integral_zero] using hd
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hroot


end
end HartreeF.FreeFlow
