import FOrdinaryFreeScalarGenerator

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace Retarded FreeTestBounds SobolevStretch StationarySelfTest

/-- Joint integrability comes from the genuine L1 source and the already proved
uniform L6 free-test bound. No abstract kernel integrability is assumed. -/
theorem actualFreeKernel_prod_integrable (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (f : ℝ → SourceSpace)
    (hf : IntegrableOn f (Set.Icc a b)) (φ : Test) :
    Integrable (fun z : ℝ × ℝ => Lp.toTemperedDistribution (f z.1)
      (freeTest (z.2-z.1) φ))
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b))) := by
  let μ := volume.restrict (Set.Icc a b)
  let P : ℝ × ℝ → EnergySpace.L6 := fun z => (freeTest (z.2-z.1) φ).toLp 6 volume
  have hP : Continuous P := (freeTest_L6_continuous hDensity hSob φ).comp
    (continuous_snd.sub continuous_fst)
  have hi := sourcePairCLM.integrable_of_bilin_of_bdd_left
    (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm (schwartzEnergyState φ))
    (μ := μ.prod μ) hP.aestronglyMeasurable
    (Eventually.of_forall (fun z => freeTest_L6_norm_le hDensity hSob (z.2-z.1) φ))
    (hf.comp_fst μ)
  exact hi.congr (Eventually.of_forall (fun z =>
    sourcePairCLM_test (freeTest (z.2-z.1) φ) (f z.1)))

theorem timeTest_deriv_norm_le (η : TimeTest) (t : ℝ) :
    ‖deriv η t‖ ≤ SchwartzMap.seminorm ℝ 0 1 η := by
  simpa only [pow_zero, one_mul, iteratedDeriv_one] using
    SchwartzMap.le_seminorm' ℝ 0 1 η t

/-- Both derivative and Laplacian terms of the literal weak kernel are integrable
on the complete time square, so restricting to its triangle and using Fubini is valid. -/
theorem actualKernelWeakTest_prod_integrable (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (f : ℝ → SourceSpace)
    (hf : IntegrableOn f (Set.Icc a b)) (η : TimeTest) (φ : Test) :
    Integrable (fun z : ℝ × ℝ => kernelWeakTest (Lp.toTemperedDistribution (f z.1)) η φ z.1 z.2)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b))) := by
  have h1 := (actualFreeKernel_prod_integrable hDensity hSob f hf φ).bdd_mul
    (((η.smooth 1).continuous_deriv_one).comp continuous_snd).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℝ × ℝ => timeTest_deriv_norm_le η z.2))
  have h2 := (actualFreeKernel_prod_integrable hDensity hSob f hf (Δ φ)).bdd_mul
    (η.continuous.comp continuous_snd).aestronglyMeasurable
    (Eventually.of_forall (fun z : ℝ × ℝ => SchwartzMap.norm_le_seminorm ℝ η z.2))
  apply ((h1.const_mul (-Complex.I)).add h2).congr
  exact Eventually.of_forall (fun z => by simp only [Pi.add_apply, Function.comp_def,
    kernelWeakTest, mul_assoc])

end HartreeF.LinearWeakEquation
