import DirectionalCandidateMeasurable
import Mathlib.MeasureTheory.Integral.Prod
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain WeakHartreeChain DerivativeMajorization
open scoped ENNReal NNReal

/-- A measurable representative on time × space suffices; slice integrability is
not needed for the totalized Bochner convolution. -/
theorem joint_riesz_measurable {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (alpha c : ℝ) (f : T → Space → ℝ)
    (hf : AEStronglyMeasurable (fun z : T × Space => f z.1 z.2) (mu.prod volume)) :
    AEStronglyMeasurable (fun z : T × Space => rieszConvolution alpha c (f z.1) z.2)
      (mu.prod volume) := by
  let f0 := hf.mk (fun z : T × Space => f z.1 z.2)
  have hm : Measurable (fun z : (T × Space) × Space =>
      rieszKernel alpha c (z.1.2-z.2)) :=
    measurable_const.mul ((measurable_fst.snd.sub measurable_snd).norm.pow_const _)
  have hg : StronglyMeasurable (fun z : (T × Space) × Space =>
      rieszKernel alpha c (z.1.2-z.2) * f0 (z.1.1, z.2)) :=
    hm.stronglyMeasurable.mul (hf.stronglyMeasurable_mk.comp_measurable
      (measurable_fst.fst.prodMk measurable_snd))
  have hs : ∀ᵐ t ∂mu, ∀ᵐ y ∂volume, f t y = f0 (t, y) :=
    MeasureTheory.Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hz : ∀ᵐ (z : T × Space) ∂mu.prod volume, ∀ᵐ y ∂volume, f z.1 y = f0 (z.1, y) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := mu) (ν := volume)).ae hs
  apply (hg.integral_prod_right' (ν := volume)).aestronglyMeasurable.congr
  filter_upwards [hz] with z hz
  change (∫ y, rieszKernel alpha c (z.2-y) * f0 (z.1, y)) =
    ∫ y, rieszKernel alpha c (z.2-y) * f z.1 y
  apply integral_congr_ae
  filter_upwards [hz] with y hy
  rw [hy]

end HartreeF.TimeHolder
