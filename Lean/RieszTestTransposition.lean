import RieszKernelTestCalculus

/-! Genuine product-measure absolute integrability and Fubini transposition for
Riesz pairing, produced by ordinary strong HLS and Holder. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
namespace HartreeF.RieszWeakDerivative
open ForcingDomain

def rieszTestPair (α c : ℝ) (f φ : Space → ℝ) (z : Space × Space) : ℝ :=
  rieszKernel α c (z.1-z.2)*f z.2*φ z.1

theorem rieszKernel_nonneg {α c : ℝ} (hc : 0 ≤ c) (z : Space) : 0 ≤ rieszKernel α c z := by
  unfold rieszKernel
  positivity

theorem rieszKernel_swap (α c : ℝ) (x y : Space) : rieszKernel α c (x-y) = rieszKernel α c (y-x) := by
  simp only [rieszKernel,norm_sub_rev]

theorem rieszTestPair_measurable {α c : ℝ} {f φ : Space → ℝ}
    (hf : AEStronglyMeasurable f volume) (hφ : AEStronglyMeasurable φ volume) :
    AEStronglyMeasurable (rieszTestPair α c f φ) (volume.prod volume) := by
  have hk := (rieszKernel_measurable α c).comp (continuous_fst.sub continuous_snd).measurable
  exact (hk.aestronglyMeasurable.mul hf.comp_snd).mul hφ.comp_fst

theorem rieszTestPair_integrable {α c p q : ℝ} (hH : OrdinaryHLS α c)
    (hp : 1 < p) (hpα : p < 3/α) (hq : 0 < q) (hrel : 1/q = 1/p-α/3)
    {s : ℝ≥0∞} [ENNReal.HolderTriple (ENNReal.ofReal q) s 1]
    {f φ : Space → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume) (hφ : MemLp φ s volume) :
    Integrable (rieszTestPair α c f φ) (volume.prod volume) := by
  obtain ⟨C,hC⟩ := hH.strong_bound p q hp hpα hq hrel
  have hdf := (hC f hf).1
  have hpn := (hC (fun y => ‖f y‖) hf.norm).2.1
  have hdom := hpn.integrable_mul hφ.norm
  apply (integrable_prod_iff (rieszTestPair_measurable hf.aestronglyMeasurable hφ.aestronglyMeasurable)).mpr
  constructor
  · filter_upwards [hdf] with x hx
    exact hx.mul_const (φ x)
  · apply hdom.congr
    filter_upwards [] with x
    have hn (y : Space) : ‖rieszTestPair α c f φ (x,y)‖ =
        rieszKernel α c (x-y)*‖f y‖*‖φ x‖ := by
      simp only [rieszTestPair,norm_mul,Real.norm_eq_abs,
        abs_of_nonneg (rieszKernel_nonneg hH.normalization_pos.le (x-y))]
    simp_rw [hn]
    rw [integral_mul_const]
    rfl

theorem riesz_test_transpose {α c p q : ℝ} (hH : OrdinaryHLS α c)
    (hp : 1 < p) (hpα : p < 3/α) (hq : 0 < q) (hrel : 1/q = 1/p-α/3)
    {s : ℝ≥0∞} [ENNReal.HolderTriple (ENNReal.ofReal q) s 1]
    {f φ : Space → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume) (hφ : MemLp φ s volume) :
    (∫ x, rieszConvolution α c f x*φ x) = (∫ y, f y*rieszConvolution α c φ y) := by
  have hpint := rieszTestPair_integrable hH hp hpα hq hrel hf hφ
  calc
    _ = ∫ x, ∫ y, rieszTestPair α c f φ (x,y) := by
      unfold rieszTestPair rieszConvolution
      simp only [integral_mul_const]
    _ = ∫ y, ∫ x, rieszTestPair α c f φ (x,y) := integral_integral_swap hpint
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      unfold rieszConvolution
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [rieszTestPair,rieszKernel_swap α c x y]
      ring

#print axioms rieszKernel_nonneg
#print axioms rieszKernel_swap
#print axioms rieszTestPair_measurable
#print axioms rieszTestPair_integrable
#print axioms riesz_test_transpose
end HartreeF.RieszWeakDerivative
