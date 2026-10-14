import WeakLeibnizH1Factor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped RealInnerProductSpace Topology
namespace HartreeF.WeakHartreeProduct
open SobolevStretch

theorem hasWeakGradient_of_locally_dominated_limit
    {f : Space → ℝ} {G : Space → Space} {fn : ℕ → Space → ℝ} {Gn : ℕ → Space → Space}
    {M N : Space → ℝ} (hf : LocallyIntegrable f volume) (hG : LocallyIntegrable G volume)
    (hM : LocallyIntegrable M volume) (hN : LocallyIntegrable N volume)
    (hw : ∀ n, HasWeakGradient (fn n) (Gn n))
    (hfbound : ∀ n, ∀ᵐ x ∂volume, ‖fn n x‖ ≤ M x)
    (hGbound : ∀ n, ∀ᵐ x ∂volume, ‖Gn n x‖ ≤ N x)
    (hft : ∀ᵐ x ∂volume, Tendsto (fun n => fn n x) atTop (𝓝 (f x)))
    (hGt : ∀ᵐ x ∂volume, Tendsto (fun n => Gn n x) atTop (𝓝 (G x))) :
    HasWeakGradient f G := by
  refine ⟨hf,hG,?_⟩
  intro v φ hφ hc
  have hd := (hφ.continuous_fderiv (by simp)).clm_apply (continuous_const (y := v))
  have hML : Integrable (fun x => M x*‖fderiv ℝ φ x v‖) volume :=
    hM.integrable_smul_right_of_hasCompactSupport hd.norm (hc.fderiv_apply ℝ v).norm
  have hNR : Integrable (fun x => N x*(‖v‖*‖φ x‖)) volume :=
    hN.integrable_smul_right_of_hasCompactSupport (continuous_const.mul hφ.continuous.norm) hc.norm.mul_left
  have hl : Tendsto (fun n => ∫ x, fn n x*fderiv ℝ φ x v) atTop
      (𝓝 (∫ x, f x*fderiv ℝ φ x v)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => M x*‖fderiv ℝ φ x v‖)
      (fun n => (hw n).function_local.aestronglyMeasurable.mul hd.aestronglyMeasurable) hML
    · intro n
      filter_upwards [hfbound n] with x hx
      change ‖fn n x*fderiv ℝ φ x v‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · filter_upwards [hft] with x hx
      exact hx.mul_const _
  have hr : Tendsto (fun n => ∫ x, ⟪Gn n x,v⟫*φ x) atTop
      (𝓝 (∫ x, ⟪G x,v⟫*φ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => N x*(‖v‖*‖φ x‖))
      (fun n => (((innerSL ℝ v).continuous.comp_aestronglyMeasurable
        (hw n).gradient_local.aestronglyMeasurable).mul hφ.continuous.aestronglyMeasurable).congr
          (ae_of_all _ (fun x => by simp only [Pi.mul_apply,innerSL_apply_apply,real_inner_comm]))) hNR
    · intro n
      filter_upwards [hGbound n] with x hx
      rw [norm_mul]
      calc
        _ ≤ (‖Gn n x‖*‖v‖)*‖φ x‖ := mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
        _ ≤ (N x*‖v‖)*‖φ x‖ := by gcongr
        _ = _ := by ring
    · filter_upwards [hGt] with x hx
      exact (hx.inner tendsto_const_nhds).mul_const _
  apply tendsto_nhds_unique hl
  convert hr.neg using 1
  funext n
  exact (hw n).integration_by_parts v φ hφ hc

#print axioms hasWeakGradient_of_locally_dominated_limit
end HartreeF.WeakHartreeProduct
