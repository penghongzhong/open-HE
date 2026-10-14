import FFreeCylinderDomains
import FPhysicalCutoffKernelBounds
import FCriticalPathSpace
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Literal low-frequency point functionals and finite-cylinder dominated convergence.
Static uncompiled draft. The weak tests are real-Hilbert tests on genuine scalar L2. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.FreeLocalCompactness
open MeasureTheory Filter FourierTransform
open scoped ENNReal Topology SchwartzMap
open FreeFlow ActualStrichartz PhysicalLowpass EnergySpace.Highpass

/-- A bounded evaluation of the actual convolution integral, not evaluation on L-infinity classes. -/
def convolutionPointCLM (k : Test) (x : V) : L2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => convolutionValue k f x
      map_add' := fun f g => convolutionValue_add (r := 2) k f g x
      map_smul' := fun c f => convolutionValue_smul k c f x }
    ‖k.toLp 2 volume‖ (fun f => convolutionValue_norm (r := 2) k f x)

theorem convolutionPointCLM_apply (k : Test) (x : V) (f : L2) :
    convolutionPointCLM k x f = convolutionValue k f x := rfl

theorem convolutionPointCLM_bound (k : Test) (x : V) (f : L2) :
    ‖convolutionPointCLM k x f‖ ≤ ‖k.toLp 2 volume‖ * ‖f‖ :=
  convolutionValue_norm (r := 2) k f x

/-- Real Riesz representation consumes exactly the real weak tests in the profile interface. -/
theorem realCLM_tendsto_zero_of_weak {f : ℕ → L2}
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    (A : L2 →L[ℝ] ℝ) : Tendsto (fun n => A (f n)) atTop (𝓝 0) := by
  let v : L2 := (InnerProductSpace.toDual ℝ L2).symm A
  have he (n : ℕ) : A (f n) = inner ℝ (f n) v := by
    rw [real_inner_comm]
    exact (InnerProductSpace.toDual_symm_apply (x := f n) (y := A)).symm
  simpa only [he] using hweak v

theorem complexCLM_tendsto_zero_of_weak {f : ℕ → L2}
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    (A : L2 →L[ℂ] ℂ) : Tendsto (fun n => A (f n)) atTop (𝓝 0) := by
  have hr := realCLM_tendsto_zero_of_weak hweak
    (Complex.reCLM.comp (A.restrictScalars ℝ))
  have hi := realCLM_tendsto_zero_of_weak hweak
    (Complex.imCLM.comp (A.restrictScalars ℝ))
  change Tendsto (fun n => (A (f n)).re) atTop (𝓝 0) at hr
  change Tendsto (fun n => (A (f n)).im) atTop (𝓝 0) at hi
  have hh := ((Complex.continuous_ofReal.tendsto 0).comp hr).add
    (((Complex.continuous_ofReal.tendsto 0).comp hi).mul_const Complex.I)
  simpa only [Function.comp_def, Complex.re_add_im, Complex.ofReal_zero, zero_mul,
    add_zero] using hh

/-- Integration of the actual joint representative supplies joint measurability. -/
def lowField (k : Test) (f : L2) (t : ℝ) (x : V) : ℂ :=
  ∫ y : V, freeJoint f t y * k (x - y)

theorem lowField_stronglyMeasurable (k : Test) (f : L2) :
    StronglyMeasurable (Function.uncurry (lowField k f)) := by
  have hm : StronglyMeasurable (fun p : (ℝ × V) × V =>
      freeJoint f p.1.1 p.2 * k (p.1.2 - p.2)) :=
    ((freeJoint_stronglyMeasurable f).comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (k.continuous.comp ((continuous_snd.comp continuous_fst).sub
        continuous_snd)).stronglyMeasurable
  exact hm.integral_prod_right'

theorem lowField_integrable (k : Test) (f : L2) (t : ℝ) (x : V) :
    Integrable (fun y : V => freeJoint f t y * k (x - y)) volume := by
  apply (convolutionValue_integrable (r := 2) k (freeL2 t f) x).congr
  filter_upwards [freeJoint_slice f t] with y hy
  rw [hy]

theorem lowField_eq_pointCLM (k : Test) (f : L2) (t : ℝ) (x : V) :
    lowField k f t x = convolutionPointCLM k x (freeL2 t f) := by
  apply integral_congr_ae
  filter_upwards [freeJoint_slice f t] with y hy
  rw [hy]

theorem lowField_bound (k : Test) (f : L2) (t : ℝ) (x : V) :
    ‖lowField k f t x‖ ≤ ‖k.toLp 2 volume‖ * ‖f‖ := by
  rw [lowField_eq_pointCLM]
  exact (convolutionPointCLM_bound k x (freeL2 t f)).trans_eq
    (by rw [freeL2_norm])

theorem lowField_pointwise_tendsto_zero (k : Test) {f : ℕ → L2}
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    (t : ℝ) (x : V) : Tendsto (fun n => lowField k (f n) t x) atTop (𝓝 0) := by
  simpa only [lowField_eq_pointCLM, ContinuousLinearMap.comp_apply] using
    complexCLM_tendsto_zero_of_weak hweak ((convolutionPointCLM k x).comp (freeL2 t))

/-- Actual smooth Fourier multipliers commute before representatives are compared. -/
theorem lowL2_freeL2 (q : Cutoff) {L : ℝ} (hL : 0 < L) (t : ℝ) (f : L2) :
    lowL2 q L (freeL2 t f) = freeL2 t (lowL2 q L f) := by
  apply l2_distribution_injective
  rw [lowL2_distribution q hL, freeL2_distribution,
    freeL2_distribution, lowL2_distribution q hL]
  unfold low FreeFlow.free
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (phase_temperate t) (lowSymbol_temperate q hL),
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (lowSymbol_temperate q hL) (phase_temperate t)]
  simp only [mul_comm]

/-- Cross-exponent distribution uniqueness compares the true infinity and two classes. -/
theorem cutoff_convolution_same_lowL2 (q : Cutoff) {L : ℝ} (hL : 0 < L) (f : L2) :
    convolutionValue (YoungSource.cutoffKernel q hL) f =ᵐ[volume] lowL2 q L f := by
  have he := CriticalPathSpace.spatial_ae_eq_of_distribution_eq
    (convolutionInfinity (r := 2) (YoungSource.cutoffKernel q hL) f)
    (lowL2 q L f)
    ((cutoff_convolution_distribution (r := 2) (by norm_num) q hL f).trans
      (lowL2_distribution q hL f).symm)
  exact (convolutionInfinity_coe (r := 2) _ _).symm.trans he

theorem lowField_slice_same_free (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (f : L2) (t : ℝ) :
    lowField (YoungSource.cutoffKernel q hL) f t =ᵐ[volume]
      freeJoint (lowL2 q L f) t := by
  have he := cutoff_convolution_same_lowL2 q hL (freeL2 t f)
  rw [lowL2_freeL2 q hL] at he
  have hp : lowField (YoungSource.cutoffKernel q hL) f t =ᵐ[volume]
      convolutionValue (YoungSource.cutoffKernel q hL) (freeL2 t f) :=
    Eventually.of_forall (fun x => lowField_eq_pointCLM _ _ _ _)
  exact hp.trans (he.trans (freeJoint_slice (lowL2 q L f) t).symm)

theorem lowField_slice_memLp (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (f : L2) (t : ℝ) : MemLp (lowField (YoungSource.cutoffKernel q hL) f t) 2 volume :=
  (memLp_congr_ae (lowField_slice_same_free q hL f t)).mpr
    (freeJoint_slice_memLp (lowL2 q L f) t)

/-- No uncountable intersection: measurable Fubini promotes each slice identity. -/
theorem lowField_cylinder_same_free (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (f : L2) (T R : ℝ) (z : V) :
    Function.uncurry (lowField (YoungSource.cutoffKernel q hL) f) =ᵐ[cylinderMeasure T R z]
      Function.uncurry (freeJoint (lowL2 q L f)) :=
  joint_ae_of_slices
    (u := lowField (YoungSource.cutoffKernel q hL) f)
    (v := freeJoint (lowL2 q L f))
    (lowField_stronglyMeasurable _ f)
    (by
      unfold Function.uncurry
      exact freeJoint_stronglyMeasurable (lowL2 q L f))
    (lowField_slice_same_free q hL f) T R z

theorem lowField_cylinder_memLp (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (f : L2) (T R : ℝ) (z : V) :
    MemLp (Function.uncurry (lowField (YoungSource.cutoffKernel q hL) f)) 2
      (cylinderMeasure T R z) :=
  (memLp_congr_ae (lowField_cylinder_same_free q hL f T R z)).mpr
    (freeJoint_cylinder_memLp (lowL2 q L f) T R z)

/-- Fixed-frequency domination is used only on the finite cylinder. -/
theorem lowField_cylinder_integral_tendsto_zero (k : Test) {f : ℕ → L2} {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ n, ‖f n‖ ≤ B)
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    (T R : ℝ) (z : V) :
    Tendsto (fun n => ∫ p : ℝ × V, ‖lowField k (f n) p.1 p.2‖ ^ 2
      ∂cylinderMeasure T R z) atTop (𝓝 0) := by
  have hd := tendsto_integral_filter_of_dominated_convergence
    (μ := cylinderMeasure T R z) (l := atTop)
    (F := fun n p => ‖lowField k (f n) p.1 p.2‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (fun _ => (‖k.toLp 2 volume‖ * B) ^ 2)
    (Eventually.of_forall (fun n =>
      ((lowField_stronglyMeasurable k (f n)).norm.pow 2).aestronglyMeasurable))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := (lowField_bound k (f n) p.1 p.2).trans
        (mul_le_mul_of_nonneg_left (hbound n) (norm_nonneg _))
      have hc : 0 ≤ ‖k.toLp 2 volume‖ * B := mul_nonneg (norm_nonneg _) hB
      exact (sq_le_sq₀ (norm_nonneg _) hc).mpr hb)))
    (integrable_const _) (Eventually.of_forall (fun p => by
      simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        (lowField_pointwise_tendsto_zero k hweak p.1 p.2).norm.pow 2))
  simpa only [integral_zero] using hd

theorem lowL2_cylinder_integral_tendsto_zero (q : Cutoff) {L : ℝ} (hL : 0 < L)
    {f : ℕ → L2} {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ n, ‖f n‖ ≤ B)
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    (T R : ℝ) (z : V) :
    Tendsto (fun n => ∫ p : ℝ × V, ‖freeJoint (lowL2 q L (f n)) p.1 p.2‖ ^ 2
      ∂cylinderMeasure T R z) atTop (𝓝 0) := by
  have he (n : ℕ) :
      (∫ p : ℝ × V, ‖lowField (YoungSource.cutoffKernel q hL) (f n) p.1 p.2‖ ^ 2
        ∂cylinderMeasure T R z) =
      ∫ p : ℝ × V, ‖freeJoint (lowL2 q L (f n)) p.1 p.2‖ ^ 2
        ∂cylinderMeasure T R z :=
    integral_congr_ae ((lowField_cylinder_same_free q hL (f n) T R z).fun_comp
      (fun a : ℂ => ‖a‖ ^ 2))
  simpa only [he] using
    lowField_cylinder_integral_tendsto_zero (YoungSource.cutoffKernel q hL) hB hbound hweak T R z

theorem lowL2_local_tendsto_zero (q : Cutoff) {L : ℝ} (hL : 0 < L)
    {f : ℕ → L2} {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ n, ‖f n‖ ≤ B)
    (hweak : ∀ v : L2, Tendsto (fun n => inner ℝ (f n) v) atTop (𝓝 0))
    (T R : ℝ) (z : V) :
    Tendsto (fun n => eLpNorm (Function.uncurry (freeJoint (lowL2 q L (f n)))) 2
      (cylinderMeasure T R z)) atTop (𝓝 0) := by
  have h := (ENNReal.continuous_ofReal.tendsto (Real.sqrt 0)).comp
    ((Real.continuous_sqrt.tendsto 0).comp
      (lowL2_cylinder_integral_tendsto_zero q hL hB hbound hweak T R z))
  have he (n : ℕ) := eLpNorm_two_eq_ofReal_sqrt
    (freeJoint_cylinder_memLp (lowL2 q L (f n)) T R z)
  simp only [he]
  simpa only [Function.comp_def, Function.uncurry, Real.sqrt_zero, ENNReal.ofReal_zero] using h

end HartreeF.FreeLocalCompactness
