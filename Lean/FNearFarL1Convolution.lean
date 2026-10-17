import FRieszNearFarKernel
import FActualL1LpConvolution
import Mathlib.Analysis.Convolution

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Convolution
namespace HartreeF.RieszL1LocalDomains

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actualConvolution_aestronglyMeasurable {h : Space → ℝ} {k : Space → E}
    (hh : AEStronglyMeasurable h volume) (hk : AEStronglyMeasurable k volume) :
    AEStronglyMeasurable (actualConvolution h k) volume := by
  exact hh.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hk

theorem bounded_kernel_section_integrable {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hk : AEStronglyMeasurable k volume)
    (hb : ∀ z, ‖k z‖ ≤ C) (x : Space) :
    Integrable (fun y => h y • k (x-y)) volume := by
  exact hh.smul_bdd C
    (hk.comp_measurePreserving ((volume : Measure Space).measurePreserving_sub_left x))
    (Eventually.of_forall fun y => hb (x-y))

theorem bounded_kernel_convolution_norm_le {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hb : ∀ z, ‖k z‖ ≤ C) (x : Space) :
    ‖actualConvolution h k x‖ ≤ C * ∫ y, ‖h y‖ := by
  calc
    _ ≤ ∫ y, ‖h y‖ * C := by
      apply norm_integral_le_of_norm_le (hh.norm.mul_const C)
      filter_upwards [] with y
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hb (x-y)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const, mul_comm]

theorem bounded_kernel_convolution_memLp_top {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hk : AEStronglyMeasurable k volume)
    (hb : ∀ z, ‖k z‖ ≤ C) : MemLp (actualConvolution h k) ∞ volume :=
  memLp_top_of_bound (actualConvolution_aestronglyMeasurable hh.aestronglyMeasurable hk)
    (C * ∫ y, ‖h y‖) (Eventually.of_forall (bounded_kernel_convolution_norm_le hh hb))

/-- All actual sections and the integral splitting live on one explicit full-measure set. -/
theorem near_far_convolution_ae {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hk : AEStronglyMeasurable k volume)
    (hn : Integrable (nearPart k) volume) (hb : ∀ z, ‖farPart k z‖ ≤ C) :
    ∀ᵐ x ∂volume,
      Integrable (fun y => h y • nearPart k (x-y)) volume ∧
      Integrable (fun y => h y • farPart k (x-y)) volume ∧
      Integrable (fun y => h y • k (x-y)) volume ∧
      actualConvolution h k x =
        actualConvolution h (nearPart k) x + actualConvolution h (farPart k) x := by
  have hnAE := hh.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hn
  filter_upwards [hnAE] with x hx
  have hnear : Integrable (fun y => h y • nearPart k (x-y)) volume := hx
  have hfar := bounded_kernel_section_integrable hh (farPart_aestronglyMeasurable hk) hb x
  have heq : (fun y => h y • k (x-y)) =
      (fun y => h y • nearPart k (x-y) + h y • farPart k (x-y)) := by
    funext y
    rw [← smul_add, nearPart_add_farPart]
  refine ⟨hnear, hfar, ?_, ?_⟩
  · rw [heq]
    exact hnear.add hfar
  · unfold actualConvolution
    rw [heq, integral_add hnear hfar]

theorem near_far_convolution_locallyIntegrable {h : Space → ℝ} {k : Space → E} {C : ℝ}
    (hh : Integrable h volume) (hk : AEStronglyMeasurable k volume)
    (hn : Integrable (nearPart k) volume) (hb : ∀ z, ‖farPart k z‖ ≤ C) :
    LocallyIntegrable (actualConvolution h k) volume := by
  have hnear : Integrable (actualConvolution h (nearPart k)) volume :=
    hh.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hn
  have hfar := bounded_kernel_convolution_memLp_top hh (farPart_aestronglyMeasurable hk) hb
  apply (hnear.locallyIntegrable.add (hfar.locallyIntegrable (by simp))).congr
  filter_upwards [near_far_convolution_ae hh hk hn hb] with x hx
  exact hx.2.2.2.symm

end HartreeF.RieszL1LocalDomains
