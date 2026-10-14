import FFreeFlowCore
import FOrdinaryHomogeneousStrichartz
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L2Space

/-!
The ordinary L1-intersection-L2 integral/unitary Fourier bridge on the actual
three-dimensional F space. This is an uncompiled static candidate. The proof
uses compact smooth distribution tests and the fundamental lemma. It imports
no BWork or D project module.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform Filter
open scoped SchwartzMap ContDiff ENNReal
namespace HartreeF.FreeLocalCompactness
open FreeFlow

/-- The integral Fourier transform agrees with the native unitary L2 class. -/
theorem fourierIntegral_ae_L2 {a : V → ℂ} (ha : Integrable a)
    (ha2 : MemLp a 2) :
    (fun x => (𝓕 (ha2.toLp a) : L2) x) =ᵐ[volume] 𝓕 a := by
  let U : L2 := 𝓕 (ha2.toLp a)
  have hFc : Continuous (𝓕 a) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ ha
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp U).locallyIntegrable (by norm_num)) hFc.locallyIntegrable
  intro g hg hc
  have hcC : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hgC : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : SchwartzMap V ℂ := hcC.toSchwartzMap hgC
  change (∫ x, φ x * U x) = ∫ x, φ x * 𝓕 a x
  calc
    _ = Lp.toTemperedDistribution U φ := by
      rw [Lp.toTemperedDistribution_apply]
      rfl
    _ = (𝓕 (Lp.toTemperedDistribution (ha2.toLp a))) φ := by
      rw [Lp.fourier_toTemperedDistribution_eq]
    _ = ∫ x, (𝓕 φ) x * a x := by
      simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [ha2.coeFn_toLp] with x hx
      rw [hx]
      rfl
    _ = ∫ x, φ x * 𝓕 a x := by
      simpa [SchwartzMap.fourier_coe, Real.fourier_eq,
        VectorFourier.fourierIntegral, real_inner_comm] using
        (VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := innerₗ V) (μ := volume) (ν := volume)
          Real.continuous_fourierChar continuous_inner φ.integrable ha)

/-- The inverse integral bridge is proved independently, with the negative
bilinear form, so it does not require integrability of the Fourier transform. -/
theorem inverseFourierIntegral_ae_L2 {a : V → ℂ} (ha : Integrable a)
    (ha2 : MemLp a 2) :
    (fun x => (𝓕⁻ (ha2.toLp a) : L2) x) =ᵐ[volume] 𝓕⁻ a := by
  let U : L2 := 𝓕⁻ (ha2.toLp a)
  have hFc : Continuous (𝓕⁻ a) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact (continuous_inner.neg :
        Continuous (fun p : V × V => -inner ℝ p.1 p.2))) ha
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp U).locallyIntegrable (by norm_num)) hFc.locallyIntegrable
  intro g hg hc
  have hcC : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hgC : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : SchwartzMap V ℂ := hcC.toSchwartzMap hgC
  change (∫ x, φ x * U x) = ∫ x, φ x * 𝓕⁻ a x
  calc
    _ = Lp.toTemperedDistribution U φ := by
      rw [Lp.toTemperedDistribution_apply]
      rfl
    _ = (𝓕⁻ (Lp.toTemperedDistribution (ha2.toLp a))) φ := by
      rw [Lp.fourierInv_toTemperedDistribution_eq]
    _ = ∫ x, (𝓕⁻ φ) x * a x := by
      simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [ha2.coeFn_toLp] with x hx
      rw [hx]
      rfl
    _ = ∫ x, φ x * 𝓕⁻ a x := by
      simpa [SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
        VectorFourier.fourierIntegral, real_inner_comm] using
        (VectorFourier.integral_fourierIntegral_smul_eq_flip
          (L := -innerₗ V) (μ := volume) (ν := volume)
          Real.continuous_fourierChar
          (by exact (continuous_inner.neg :
            Continuous (fun p : V × V => -inner ℝ p.1 p.2)))
          φ.integrable ha)

theorem inverseFourierIntegral_memLp {a : V → ℂ} (ha : Integrable a)
    (ha2 : MemLp a 2) : MemLp (𝓕⁻ a) 2 :=
  (Lp.memLp (𝓕⁻ (ha2.toLp a))).ae_eq (inverseFourierIntegral_ae_L2 ha ha2)

/-- The real squared norm of a genuine L2 class is its literal square integral. -/
theorem L2_integral_sq_norm (f : L2) : (∫ x, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  calc
    _ = ∫ x, inner ℝ (f x) (f x) := by
      simp only [real_inner_self_eq_norm_sq]
    _ = inner ℝ f f := (MeasureTheory.L2.inner_def f f).symm
    _ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f

theorem integral_sq_norm_toLp {a : V → ℂ} (ha2 : MemLp a 2) :
    (∫ x, ‖a x‖ ^ 2) = ‖ha2.toLp a‖ ^ 2 := by
  rw [← L2_integral_sq_norm]
  apply integral_congr_ae
  filter_upwards [ha2.coeFn_toLp] with x hx
  rw [hx]

/-- True integral Plancherel, after the integral's L2 domain has been proved. -/
theorem inverseFourierIntegral_plancherel {a : V → ℂ} (ha : Integrable a)
    (ha2 : MemLp a 2) :
    (∫ x, ‖𝓕⁻ a x‖ ^ 2) = ∫ x, ‖a x‖ ^ 2 := by
  have hnorm : ‖(𝓕⁻ (ha2.toLp a) : L2)‖ = ‖ha2.toLp a‖ := by
    simpa only [fourier_fourierInv_eq] using
      (Lp.norm_fourier_eq (𝓕⁻ (ha2.toLp a))).symm
  calc
    _ = ∫ x, ‖(𝓕⁻ (ha2.toLp a) : L2) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [inverseFourierIntegral_ae_L2 ha ha2] with x hx
      rw [hx]
    _ = ‖ha2.toLp a‖ ^ 2 := by rw [L2_integral_sq_norm, hnorm]
    _ = ∫ x, ‖a x‖ ^ 2 := (integral_sq_norm_toLp ha2).symm

/-- The explicit integral representative, whose values on coordinate
hyperplanes are meaningful for every fixed coordinate. -/
def integralEvolution (a : V → ℂ) (t : ℝ) (x : V) : ℂ :=
  𝓕⁻ (fun ξ => phase t ξ * a ξ) x

theorem phase_mul_integrable {a : V → ℂ} (ha : Integrable a) (t : ℝ) :
    Integrable (fun ξ => phase t ξ * a ξ) := by
  apply ha.mono ((phase_memLp t).aestronglyMeasurable.mul ha.aestronglyMeasurable)
  exact Eventually.of_forall (fun ξ => by
    change ‖phase t ξ * a ξ‖ ≤ ‖a ξ‖
    rw [norm_mul, phase_norm, one_mul])

theorem phase_mul_memLp {a : V → ℂ} (ha2 : MemLp a 2) (t : ℝ) :
    MemLp (fun ξ => phase t ξ * a ξ) 2 := by
  apply ha2.of_le ((phase_memLp t).aestronglyMeasurable.mul ha2.aestronglyMeasurable)
  exact Eventually.of_forall (fun ξ => by
    change ‖phase t ξ * a ξ‖ ≤ ‖a ξ‖
    rw [norm_mul, phase_norm, one_mul])

theorem phase_mul_toLp {a : V → ℂ} (ha2 : MemLp a 2) (t : ℝ) :
    (phase_mul_memLp ha2 t).toLp (fun ξ => phase t ξ * a ξ) =
      phaseMultiply t (ha2.toLp a) := by
  apply Lp.ext
  filter_upwards [(phase_mul_memLp ha2 t).coeFn_toLp,
    phaseMultiply_coe t (ha2.toLp a), ha2.coeFn_toLp] with ξ h₁ h₂ h₃
  exact h₁.trans (h₂.trans (by rw [h₃])).symm

/-- Each time slice identifies the explicit integral with the genuine freeL2
class. This is the second necessary use of inverse-integral compatibility. -/
theorem integralEvolution_ae_freeL2 {a : V → ℂ} (ha : Integrable a)
    (ha2 : MemLp a 2) (t : ℝ) :
    integralEvolution a t =ᵐ[volume] freeL2 t (𝓕⁻ (ha2.toLp a)) := by
  have h := (inverseFourierIntegral_ae_L2 (phase_mul_integrable ha t)
    (phase_mul_memLp ha2 t)).symm
  rw [phase_mul_toLp ha2 t] at h
  change integralEvolution a t =ᵐ[volume]
    (fun x => (𝓕⁻ (phaseMultiply t (𝓕 (𝓕⁻ (ha2.toLp a)))) : L2) x)
  unfold integralEvolution
  simpa only [fourier_fourierInv_eq] using h

/-- Parameter measurability is proved for the explicit integral before using
Fubini to transport its slice identities. -/
theorem integralEvolution_stronglyMeasurable {a : V → ℂ}
    (ha : StronglyMeasurable a) :
    StronglyMeasurable (Function.uncurry (integralEvolution a)) := by
  have hi : StronglyMeasurable (fun p : (ℝ × V) × V =>
      Complex.exp (((2 * Real.pi * inner ℝ p.2 p.1.2 : ℝ) : ℂ) * Complex.I) *
        (phase p.1.1 p.2 * a p.2)) := by
    have hm : Measurable a := ha.measurable
    unfold phase
    fun_prop
  convert hi.integral_prod_right' (ν := (volume : Measure V)) using 1
  funext p
  rcases p with ⟨t, x⟩
  simp only [Function.uncurry_apply_pair, integralEvolution, Real.fourierInv_eq',
    smul_eq_mul]

/-- Every-time spatial AE equality gives product AE equality only after joint
measurability. It does not claim arbitrary-hyperplane traces of freeJoint. -/
theorem integralEvolution_ae_freeJoint {a : V → ℂ} (ha : Integrable a)
    (ha2 : MemLp a 2) (has : StronglyMeasurable a) :
    Function.uncurry (integralEvolution a) =ᵐ[volume.prod volume]
      Function.uncurry (ActualStrichartz.freeJoint (𝓕⁻ (ha2.toLp a))) := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (integralEvolution_stronglyMeasurable has).measurable
      (ActualStrichartz.freeJoint_stronglyMeasurable _).measurable)).2
  exact Eventually.of_forall (fun t =>
    (integralEvolution_ae_freeL2 ha ha2 t).trans
      (ActualStrichartz.freeJoint_slice _ t).symm)

end HartreeF.FreeLocalCompactness
