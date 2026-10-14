import FGeneralApproximationTransfer
import FMixedVectorQuantitative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalProfileProducts
open TimeHolder ProfileApproximation GeneralProfileCross

/-- Literal nonnegative overlap of two actual fields. -/
def normProduct {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : ℝ → Space → E) (g : ℝ → Space → F) : ℝ → Space → ℝ :=
  fun t x => ‖f t x‖ * ‖g t x‖

/-- P and Q use the same literal local product, with their exact spatial exponents. -/
def localProductNorm {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (q : ℝ≥0∞) (f : ℝ → Space → E) (g : ℝ → Space → F) : ℝ≥0∞ :=
  mixedNorm volume volume 5 q (normProduct f g)

/-- Two-step Hölder with finite input norms. The conversion to real slice norms occurs
only on the conull set where the genuine extended norms have already been proved finite. -/
theorem normProduct_mixed_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (hp0 : p ≠ 0) (hpT : p ≠ ∞) (hq0 : q ≠ 0) (hqT : q ≠ ∞)
    (hr0 : r ≠ 0) (hrT : r ≠ ∞)
    (f : ℝ → Space → E) (g : ℝ → Space → F)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume))
    (hff : mixedNorm volume volume 10 p f ≠ ∞)
    (hgf : mixedNorm volume volume 10 q g ≠ ∞) :
    localProductNorm r f g ≤ mixedNorm volume volume 10 p f * mixedNorm volume volume 10 q g := by
  let A : ℝ → ℝ := fun t => (eLpNorm (f t) p volume).toReal
  let B : ℝ → ℝ := fun t => (eLpNorm (g t) q volume).toReal
  have hmA := spatial_lp_time_toReal_measurable volume volume p hp0 hpT f hf
  have hmB := spatial_lp_time_toReal_measurable volume volume q hq0 hqT g hg
  have hsA := finite_mixedNorm_ae_slice_memLp volume volume 10 p (by norm_num) (by norm_num) f hff
  have hsB := finite_mixedNorm_ae_slice_memLp volume volume 10 q (by norm_num) (by norm_num) g hgf
  have hmP : AEStronglyMeasurable (fun z : ℝ × Space => normProduct f g z.1 z.2) (volume.prod volume) :=
    hf.norm.mul hg.norm
  have hslice : ∀ᵐ t ∂volume, eLpNorm (normProduct f g t) r volume ≤ ‖A t * B t‖ₑ := by
    filter_upwards [hsA,hsB] with t hft hgt
    have hh := temporal_real_product_norm (p := p) (q := q) (r := r) volume
      (fun x => ‖f t x‖) (fun x => ‖g t x‖) hft.aestronglyMeasurable.norm hgt.aestronglyMeasurable.norm
    rw [eLpNorm_norm _ hft.aestronglyMeasurable, eLpNorm_norm _ hgt.aestronglyMeasurable] at hh
    change eLpNorm (normProduct f g t) r volume ≤ _ at hh
    simpa only [A,B,Real.enorm_eq_ofReal (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hft.eLpNorm_ne_top,
      ENNReal.ofReal_toReal hgt.eLpNorm_ne_top] using hh
  let : ENNReal.HolderTriple (10 : ℝ≥0∞) 10 5 := by
    have h : Real.HolderTriple (10 : ℝ) 10 5 := by constructor <;> norm_num
    simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal
  calc
    localProductNorm r f g ≤ eLpNorm (fun t => A t * B t) 5 volume := by
      apply eLpNorm_mono_enorm_ae (spatial_lp_time_measurable volume volume r hr0 hrT _ hmP)
      simpa only [enorm_eq_self] using hslice
    _ ≤ eLpNorm A 10 volume * eLpNorm B 10 volume := temporal_real_product_norm volume A B hmA hmB
    _ = _ := by
      rw [real_slice_mixed_eq volume 10 p hp0 hpT f hf hsA,
        real_slice_mixed_eq volume 10 q hq0 hqT g hg hsB]

theorem value_product_holder : ENNReal.HolderTriple (10 : ℝ≥0∞) 10 5 := by
  have h : Real.HolderTriple (10 : ℝ) 10 5 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal

theorem value_gradient_product_holder :
    ENNReal.HolderTriple (10 : ℝ≥0∞) (ENNReal.ofReal (30/13 : ℝ)) (ENNReal.ofReal (15/8 : ℝ)) := by
  have h : Real.HolderTriple (10 : ℝ) (30/13) (15/8) := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat] using h.ennrealOfReal

/-- The actual value-value overlap has no additional analytic premise. -/
theorem P_le (u v : ℝ → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume))
    (huS : mixedNorm volume volume 10 10 u ≠ ∞) (hvS : mixedNorm volume volume 10 10 v ≠ ∞) :
    localProductNorm 5 u v ≤ mixedNorm volume volume 10 10 u * mixedNorm volume volume 10 10 v := by
  let := value_product_holder
  exact normProduct_mixed_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) u v hu hv huS hvS

theorem Q_le {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (u : ℝ → Space → ℂ) (H : ℝ → Space → F)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) (volume.prod volume))
    (huS : mixedNorm volume volume 10 10 u ≠ ∞)
    (hHW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) H ≠ ∞) :
    localProductNorm (ENNReal.ofReal (15/8 : ℝ)) u H ≤
      mixedNorm volume volume 10 10 u * mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) H := by
  let := value_gradient_product_holder
  exact normProduct_mixed_le (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) u H hu hH huS hHW

#print axioms normProduct_mixed_le
#print axioms P_le
#print axioms Q_le
end HartreeF.LocalProfileProducts
