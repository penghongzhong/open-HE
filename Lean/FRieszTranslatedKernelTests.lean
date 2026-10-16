import FRieszKernelDerivative
import RieszTestTransposition

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.RieszConvolutionDerivative
open ForcingDomain RieszWeakDerivative RieszKernelDerivative SobolevStretch

/-- Translation of a compact test in the proved singular-kernel weak relation. -/
theorem translated_kernel_integration_by_parts {α c : ℝ}
    (hα1 : 1 < α) (hα3 : α < 3) (hc : 0 < c)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (y v : Space) :
    (∫ x, rieszKernel α c (x-y) * fderiv ℝ φ x v) =
      -(∫ x, ⟪rieszKernelGradient α c (x-y),v⟫ * φ x) := by
  have hψ := hφ.comp (contDiff_id.add (contDiff_const (c := y)))
  have hψc : HasCompactSupport (fun z => φ (z+y)) :=
    hφc.comp_homeomorph (Homeomorph.addRight y)
  have hw := (rieszKernel_hasWeakGradient hα1 hα3 hc).integration_by_parts v
    (fun z => φ (z+y)) hψ hψc
  simp only [fderiv_comp_add_right] at hw
  calc
    _ = ∫ z, rieszKernel α c z * fderiv ℝ φ (z+y) v := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun x => rieszKernel α c (x-y) * fderiv ℝ φ x v) y).symm
    _ = -(∫ z, ⟪rieszKernelGradient α c z,v⟫ * φ (z+y)) := hw
    _ = _ := by
      congr 1
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun x => ⟪rieszKernelGradient α c (x-y),v⟫ * φ x) y)

/-- The genuinely absolutely integrable two-point tested gradient integrand. -/
def gradientTestPair (α c : ℝ) (f φ : Space → ℝ) (v : Space)
    (z : Space × Space) : ℝ :=
  f z.2 * ⟪rieszKernelGradient α c (z.1-z.2),v⟫ * φ z.1

theorem gradientTestPair_measurable {α c : ℝ} {f φ : Space → ℝ} (v : Space)
    (hf : AEStronglyMeasurable f volume) (hφ : AEStronglyMeasurable φ volume) :
    AEStronglyMeasurable (gradientTestPair α c f φ v) (volume.prod volume) := by
  have hk := (rieszKernelGradient_measurable α c).comp
    (continuous_fst.sub continuous_snd).measurable
  exact (hf.comp_snd.mul (hk.aestronglyMeasurable.inner aestronglyMeasurable_const)).mul hφ.comp_fst

theorem gradientTestPair_integrable {α c c' p q : ℝ}
    (hα3 : α < 3) (hc : 0 < c) (hH : OrdinaryHLS (α-1) c')
    (hp : 1 < p) (hpα : p < 3/(α-1)) (hq : 0 < q)
    (hrel : 1/q = 1/p-(α-1)/3)
    {s : ℝ≥0∞} [ENNReal.HolderTriple (ENNReal.ofReal q) s 1]
    {f φ : Space → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume)
    (hφ : MemLp φ s volume) (v : Space) :
    Integrable (gradientTestPair α c f φ v) (volume.prod volume) := by
  have hd := rieszTestPair_integrable hH hp hpα hq hrel hf.norm hφ.norm
  let A : ℝ := c * (3-α) / c'
  apply (hd.const_mul (A * ‖v‖)).mono'
    (gradientTestPair_measurable v hf.aestronglyMeasurable hφ.aestronglyMeasurable)
  filter_upwards [] with z
  change ‖f z.2 * ⟪rieszKernelGradient α c (z.1-z.2),v⟫ * φ z.1‖ ≤
    (A * ‖v‖) * (rieszKernel (α-1) c' (z.1-z.2) * ‖f z.2‖ * ‖φ z.1‖)
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖f z.2‖ * (‖rieszKernelGradient α c (z.1-z.2)‖ * ‖v‖) * ‖φ z.1‖ := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = _ := by
      rw [rieszKernelGradient_norm_eq_lowerOrder hα3 hc hH.normalization_pos]
      dsimp [A]
      ring

#print axioms translated_kernel_integration_by_parts
#print axioms gradientTestPair_integrable
end HartreeF.RieszConvolutionDerivative
