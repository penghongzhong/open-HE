import FRieszKernelDerivative
import RieszTestTransposition
import RieszTestDualDomains

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace HartreeF.RieszConvolutionDerivative
open ForcingDomain RieszWeakDerivative RieszKernelDerivative SobolevStretch

/-- The actual integral of the singular kernel gradient against the density. -/
def gradientConvolution (α c : ℝ) (f : Space → ℝ) (x : Space) : Space :=
  ∫ y, f y • rieszKernelGradient α c (x-y)

theorem gradientConvolution_aestronglyMeasurable {α c : ℝ} {f : Space → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (gradientConvolution α c f) volume := by
  have hk := (rieszKernelGradient_measurable α c).comp
    (continuous_fst.sub continuous_snd).measurable
  exact (hf.comp_snd.smul hk.aestronglyMeasurable).integral_prod_right'

theorem gradientConvolution_norm_le {α c c' : ℝ}
    (hα : α < 3) (hc : 0 < c) (hc' : 0 < c') (f : Space → ℝ) (x : Space) :
    ‖gradientConvolution α c f x‖ ≤
      (c * (3-α) / c') * rieszConvolution (α-1) c' (fun y => ‖f y‖) x := by
  calc
    _ ≤ ∫ y, ‖f y • rieszKernelGradient α c (x-y)‖ := norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [norm_smul, rieszKernelGradient_norm_eq_lowerOrder hα hc hc']
      unfold rieszConvolution
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring

theorem gradientConvolution_bound {α c c' p q : ℝ}
    (hα : α < 3) (hc : 0 < c) (hH : OrdinaryHLS (α-1) c')
    (hp : 1 < p) (hpα : p < 3/(α-1)) (hq : 0 < q)
    (hrel : 1/q = 1/p-(α-1)/3) :
    ∃ C : ℝ≥0, ∀ f : Space → ℝ, MemLp f (ENNReal.ofReal p) volume →
      (∀ᵐ x ∂volume, Integrable (fun y => f y • rieszKernelGradient α c (x-y)) volume) ∧
      MemLp (gradientConvolution α c f) (ENNReal.ofReal q) volume ∧
      eLpNorm (gradientConvolution α c f) (ENNReal.ofReal q) volume ≤
        (ENNReal.ofReal (c * (3-α) / c') * C) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC⟩ := hH.strong_bound p q hp hpα hq hrel
  refine ⟨C,?_⟩
  intro f hf
  let A : ℝ := c * (3-α) / c'
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hα.le)) hH.normalization_pos.le
  have hd := hC (fun y => ‖f y‖) hf.norm
  have hm : MemLp (fun x => A * rieszConvolution (α-1) c' (fun y => ‖f y‖) x)
      (ENNReal.ofReal q) volume := hd.2.1.const_mul A
  have hle : ∀ x, ‖gradientConvolution α c f x‖ ≤
      ‖A * rieszConvolution (α-1) c' (fun y => ‖f y‖) x‖ := by
    intro x
    exact (gradientConvolution_norm_le hα hc hH.normalization_pos f x).trans (le_abs_self _)
  refine ⟨?_, hm.of_le (gradientConvolution_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall hle), ?_⟩
  · filter_upwards [hd.1] with x hx
    apply (hx.const_mul A).mono'
      (hf.aestronglyMeasurable.smul (((rieszKernelGradient_measurable α c).comp
        (continuous_const.sub continuous_id).measurable).aestronglyMeasurable))
    filter_upwards [] with y
    change ‖f y • rieszKernelGradient α c (x-y)‖ ≤ A * (rieszKernel (α-1) c' (x-y) * ‖f y‖)
    rw [norm_smul, rieszKernelGradient_norm_eq_lowerOrder hα hc hH.normalization_pos]
    dsimp [A]
    exact le_of_eq (by ring)
  · calc
      _ ≤ eLpNorm (fun x => A * rieszConvolution (α-1) c' (fun y => ‖f y‖) x)
          (ENNReal.ofReal q) volume := eLpNorm_mono_ae (gradientConvolution_aestronglyMeasurable hf.aestronglyMeasurable) (Eventually.of_forall hle)
      _ = ENNReal.ofReal A * eLpNorm (rieszConvolution (α-1) c' (fun y => ‖f y‖))
          (ENNReal.ofReal q) volume := by
        change eLpNorm (A • rieszConvolution (α-1) c' (fun y => ‖f y‖)) _ _ = _
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hA]
      _ ≤ ENNReal.ofReal A * (C * eLpNorm f (ENNReal.ofReal p) volume) := by
        gcongr
        simpa only [eLpNorm_norm f hf.aestronglyMeasurable] using hd.2.2
      _ = (ENNReal.ofReal (c * (3-α) / c') * C) * eLpNorm f (ENNReal.ofReal p) volume := by
        exact (mul_assoc _ _ _).symm

#print axioms gradientConvolution_bound
end HartreeF.RieszConvolutionDerivative
