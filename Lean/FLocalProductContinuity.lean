import FLocalProductHolder
import FActualApproximationBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalProfileProducts
open TimeHolder ProfileApproximation GeneralProfileCross

/-- Pointwise difference control keeps the value and the independent direction labels. -/
theorem normProduct_difference_pointwise {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (u U : E) (v V : F) :
    ‖‖u‖ * ‖v‖ - ‖U‖ * ‖V‖‖ ≤ ‖u-U‖ * ‖v‖ + ‖U‖ * ‖v-V‖ := by
  have he : ‖u‖ * ‖v‖ - ‖U‖ * ‖V‖ = (‖u‖-‖U‖)*‖v‖ + ‖U‖*(‖v‖-‖V‖) := by ring
  rw [he]
  calc
    _ ≤ ‖(‖u‖-‖U‖)*‖v‖‖ + ‖‖U‖*(‖v‖-‖V‖)‖ := norm_add_le _ _
    _ = |‖u‖-‖U‖| *‖v‖ + ‖U‖* |‖v‖-‖V‖| := by simp only [norm_mul, Real.norm_eq_abs, abs_norm]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u U) (norm_nonneg v))
      (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le v V) (norm_nonneg U))

/-- Genuine local-product continuity in the exact mixed target norm. -/
theorem normProduct_difference_mixed_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (hp0 : p ≠ 0) (hpT : p ≠ ∞) (hq0 : q ≠ 0) (hqT : q ≠ ∞)
    (hr1 : 1 ≤ r) (hrT : r ≠ ∞)
    (u U : ℝ → Space → E) (v V : ℝ → Space → F)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hU : AEStronglyMeasurable (fun z : ℝ × Space => U z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume))
    (hV : AEStronglyMeasurable (fun z : ℝ × Space => V z.1 z.2) (volume.prod volume))
    (hdu : mixedNorm volume volume 10 p (fun t x => u t x-U t x) ≠ ∞)
    (hfv : mixedNorm volume volume 10 q v ≠ ∞)
    (hfU : mixedNorm volume volume 10 p U ≠ ∞)
    (hdv : mixedNorm volume volume 10 q (fun t x => v t x-V t x) ≠ ∞) :
    mixedNorm volume volume 5 r (fun t x => normProduct u v t x-normProduct U V t x) ≤
      mixedNorm volume volume 10 p (fun t x => u t x-U t x) * mixedNorm volume volume 10 q v +
      mixedNorm volume volume 10 p U * mixedNorm volume volume 10 q (fun t x => v t x-V t x) := by
  have hr0 : r ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le hr1)
  have htri := mixed_norm_le_add_of_domination volume 5 r (by norm_num) hr1 hrT
    (fun t x => normProduct u v t x-normProduct U V t x)
    (normProduct (fun t x => u t x-U t x) v)
    (normProduct U (fun t x => v t x-V t x))
    ((hu.norm.mul hv.norm).sub (hU.norm.mul hV.norm))
    ((hu.sub hU).norm.mul hv.norm) (hU.norm.mul (hv.sub hV).norm)
    (ae_of_all _ fun t => ae_of_all _ fun x => by
      simpa only [normProduct, Real.norm_eq_abs, abs_mul, abs_norm] using
        normProduct_difference_pointwise (u t x) (U t x) (v t x) (V t x))
  exact htri.trans (add_le_add
    (normProduct_mixed_le hp0 hpT hq0 hqT hr0 hrT _ v (hu.sub hU) hv hdu hfv)
    (normProduct_mixed_le hp0 hpT hq0 hqT hr0 hrT U _ hU (hv.sub hV) hfU hdv))

/-- The product norm is controlled by an actual product-difference error and the reference. -/
theorem localProductNorm_le_error_add {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hqT : q ≠ ∞)
    (u U : ℝ → Space → E) (v V : ℝ → Space → F)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hU : AEStronglyMeasurable (fun z : ℝ × Space => U z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume))
    (hV : AEStronglyMeasurable (fun z : ℝ × Space => V z.1 z.2) (volume.prod volume)) :
    localProductNorm q u v ≤
      mixedNorm volume volume 5 q (fun t x => normProduct u v t x-normProduct U V t x) +
      localProductNorm q U V :=
  mixedNorm_le_error_add (by norm_num) hq1 hqT _ _ (hu.norm.mul hv.norm) (hU.norm.mul hV.norm)

/-- Canonical representative transport needs only nested a.e. equality. -/
theorem normProduct_congr_nested_ae {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {u U : ℝ → Space → E} {v V : ℝ → Space → F}
    (hu : ∀ᵐ t ∂volume, u t =ᵐ[volume] U t) (hv : ∀ᵐ t ∂volume, v t =ᵐ[volume] V t) :
    ∀ᵐ t ∂volume, normProduct u v t =ᵐ[volume] normProduct U V t := by
  filter_upwards [hu,hv] with t hut hvt
  filter_upwards [hut,hvt] with x hux hvx
  simp only [normProduct,hux,hvx]

#print axioms normProduct_difference_mixed_le
#print axioms localProductNorm_le_error_add
#print axioms normProduct_congr_nested_ae
end HartreeF.LocalProfileProducts
