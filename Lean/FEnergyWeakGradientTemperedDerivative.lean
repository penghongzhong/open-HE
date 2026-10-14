import FEnergySchwartzExtension
import HartreeForcingDirectionalIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal RealInnerProductSpace SchwartzMap
namespace HartreeF.EnergySpace
open SobolevStretch WeakHartreeProduct

theorem complex_weak_schwartz_test {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {u : Space → ℂ} {U V : Space → Space}
    (hu : MemLp u p volume) (hU : MemLp U q volume) (hV : MemLp V q volume)
    (hwR : HasWeakGradient (fun x => (u x).re) U)
    (hwI : HasWeakGradient (fun x => (u x).im) V)
    (ψ : SchwartzMap Space ℝ) (v : Space) :
    (∫ x, (fderiv ℝ ψ x v : ℂ) * u x) =
      -(∫ x, (ψ x : ℂ) * directionalField U V v x) := by
  let := ENNReal.HolderConjugate.inv_one_sub_inv' hp
  let := ENNReal.HolderConjugate.inv_one_sub_inv' hq
  have hleft : Integrable (fun x => (fderiv ℝ ψ x v : ℂ) * u x) volume := by
    have h := hu.integrable_mul
      ((SchwartzMap.postcompCLM Complex.ofRealCLM (∂_{v} ψ)).memLp ((1-p⁻¹)⁻¹) volume)
    apply h.congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]
  have hright : Integrable (fun x => (ψ x : ℂ) * directionalField U V v x) volume := by
    have h := (directionalField_memLp hU hV v).integrable_mul
      ((SchwartzMap.postcompCLM Complex.ofRealCLM ψ).memLp ((1-q⁻¹)⁻¹) volume)
    apply h.congr
    filter_upwards [] with x
    simp only [Pi.mul_apply, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, mul_comm]
  have hr := weak_gradient_schwartz_test hp hq
    (hu.continuousLinearMap_comp Complex.reCLM) hU hwR ψ v
  have hi := weak_gradient_schwartz_test hp hq
    (hu.continuousLinearMap_comp Complex.imCLM) hV hwI ψ v
  apply Complex.ext
  · rw [Complex.neg_re]
    change Complex.reCLM _ = -Complex.reCLM _
    rw [← Complex.reCLM.integral_comp_comm hleft, ← Complex.reCLM.integral_comp_comm hright]
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      directionalField, Complex.equivRealProdCLM_symm_apply_re, mul_comm] using hr
  · rw [Complex.neg_im]
    change Complex.imCLM _ = -Complex.imCLM _
    rw [← Complex.imCLM.integral_comp_comm hleft, ← Complex.imCLM.integral_comp_comm hright]
    simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, add_zero, zero_add,
      directionalField, Complex.equivRealProdCLM_symm_apply_im, mul_comm] using hi

/-- Any actual complex weak gradient with the displayed Lp domains is the
actual tempered-distribution derivative. This applies to the energy function
and also to the Hartree source; no L2 membership of the value is required. -/
theorem weak_gradient_tempered_derivative {p q : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    [hq : Fact (1 ≤ q)] {u : Space → ℂ} {U V : Space → Space}
    (hu : MemLp u p volume) (hU : MemLp U q volume) (hV : MemLp V q volume)
    (hwR : HasWeakGradient (fun x => (u x).re) U)
    (hwI : HasWeakGradient (fun x => (u x).im) V) (v : Space) :
    ∂_{v} (Lp.toTemperedDistribution (hu.toLp u)) =
      Lp.toTemperedDistribution ((directionalField_memLp hU hV v).toLp
        (directionalField U V v)) := by
  apply temperedDistribution_ext_real_tests
  intro ψ
  have hd (x : Space) : fderiv ℝ (SchwartzMap.postcompCLM Complex.ofRealCLM ψ) x v =
      (fderiv ℝ ψ x v : ℂ) := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp x (ψ.differentiableAt.hasFDerivAt)
    change fderiv ℝ (Complex.ofRealCLM ∘ ψ) x v = _
    rw [h.fderiv]
    rfl
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have hleft : (∫ x, (- ∂_{v} (SchwartzMap.postcompCLM Complex.ofRealCLM ψ)) x •
      hu.toLp u x) = -(∫ x, (fderiv ℝ ψ x v : ℂ) * u x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with x hx
    simp only [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, hd, hx, smul_eq_mul, neg_mul]
  have hright : (∫ x, (SchwartzMap.postcompCLM Complex.ofRealCLM ψ) x •
      (directionalField_memLp hU hV v).toLp (directionalField U V v) x) =
      (∫ x, (ψ x : ℂ) * directionalField U V v x) := by
    apply integral_congr_ae
    filter_upwards [(directionalField_memLp hU hV v).coeFn_toLp] with x hx
    simp only [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply, hx, smul_eq_mul]
  rw [hleft, hright, complex_weak_schwartz_test hp.out hq.out hu hU hV hwR hwI ψ v, neg_neg]

end HartreeF.EnergySpace
