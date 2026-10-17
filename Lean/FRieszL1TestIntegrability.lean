import FNearFarL1Convolution
import FRieszTranslatedKernelTests

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.RieszL1LocalDomains
open ForcingDomain RieszWeakDerivative RieszKernelDerivative RieszConvolutionDerivative

/-- Absolute integrability of the actual two-point compact-tested convolution.
The near kernel is genuinely L1 and the far kernel has an actual pointwise bound. -/
theorem near_far_testPair_integrable {h k φ : Space → ℝ} {C : ℝ}
    (hh : Integrable h volume) (hk : AEStronglyMeasurable k volume)
    (hn : Integrable (nearPart k) volume) (hb : ∀ z, ‖farPart k z‖ ≤ C)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun z : Space × Space => k (z.1-z.2) * h z.2 * φ z.1)
      (volume.prod volume) := by
  obtain ⟨D,hD⟩ := hφ.bounded_above_of_compact_support hφc
  have hnear0 : Integrable (fun z : Space × Space => h z.2 * nearPart k (z.1-z.2))
      (volume.prod volume) :=
    hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hn
  have hnear := hnear0.mul_bdd hφ.aestronglyMeasurable.comp_fst
    (Eventually.of_forall fun z => hD z.1)
  have hfarMeas : AEStronglyMeasurable
      (fun z : Space × Space => h z.2 * farPart k (z.1-z.2) * φ z.1)
      (volume.prod volume) :=
    (hh.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
      (farPart_aestronglyMeasurable hk)).mul hφ.aestronglyMeasurable.comp_fst
  have hfar : Integrable
      (fun z : Space × Space => h z.2 * farPart k (z.1-z.2) * φ z.1)
      (volume.prod volume) := by
    apply (((hφ.integrable_of_hasCompactSupport hφc).norm.mul_prod hh.norm).const_mul C).mono'
      hfarMeas
    filter_upwards [] with z
    simp only [norm_mul]
    calc
      _ ≤ ‖h z.2‖ * C * ‖φ z.1‖ := by gcongr; exact hb (z.1-z.2)
      _ = C * (‖φ z.1‖ * ‖h z.2‖) := by ring
  apply (hnear.add hfar).congr
  filter_upwards [] with z
  change h z.2 * nearPart k (z.1-z.2) * φ z.1 +
      h z.2 * farPart k (z.1-z.2) * φ z.1 = k (z.1-z.2) * h z.2 * φ z.1
  rw [← add_mul, ← mul_add, nearPart_add_farPart]
  ring

/-- Genuine Fubini domain for a compact test of the actual Riesz potential of L1 data. -/
theorem rieszTestPair_integrable_L1 {α c : ℝ} {h φ : Space → ℝ}
    (hα : 0 < α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (rieszTestPair α c h φ) (volume.prod volume) :=
  near_far_testPair_integrable hh (rieszKernel_measurable α c).aestronglyMeasurable
    (near_rieszKernel_integrable hα) (far_rieszKernel_norm_le hα3 hc) hφ hφc

/-- The derivative test domain follows from the locally integrable lower-order kernel,
not a strong HLS statement at L1. -/
theorem gradientTestPair_integrable_L1 {α c : ℝ} {h φ : Space → ℝ}
    (hα1 : 1 < α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (v : Space) :
    Integrable (gradientTestPair α c h φ v) (volume.prod volume) := by
  have hd := rieszTestPair_integrable_L1 (α := α-1) (c := 1)
    (by linarith) (by linarith) (by norm_num) hh.norm hφ.norm hφc.norm
  let A : ℝ := c * (3-α)
  apply (hd.const_mul (A * ‖v‖)).mono'
    (gradientTestPair_measurable v hh.aestronglyMeasurable hφ.aestronglyMeasurable)
  filter_upwards [] with z
  change ‖h z.2 * ⟪rieszKernelGradient α c (z.1-z.2),v⟫ * φ z.1‖ ≤
    (A * ‖v‖) * (rieszKernel (α-1) 1 (z.1-z.2) * ‖h z.2‖ * ‖φ z.1‖)
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖h z.2‖ * (‖rieszKernelGradient α c (z.1-z.2)‖ * ‖v‖) * ‖φ z.1‖ := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = _ := by
      rw [rieszKernelGradient_norm_eq_lowerOrder hα3 hc (by norm_num : (0:ℝ)<1)]
      dsimp [A]
      ring

end HartreeF.RieszL1LocalDomains
