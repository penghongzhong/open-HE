import LocalBoundedPairChain
import HartreePowerCalculus

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped NNReal
namespace HartreeF.WeakHartreeChain
open SobolevStretch StationarySelfTest

theorem realCLM_apply_pair (L : ℂ →L[ℝ] ℝ) (w : ℝ × ℝ) :
    L (Complex.equivRealProdCLM.symm w) = L 1*w.1+L Complex.I*w.2 := by
  have he : Complex.equivRealProdCLM.symm w = w.1 • (1 : ℂ)+w.2 • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  rw [he, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

theorem hasWeakGradient_bounded_complex_comp_dotH1 (hDensity : OrdinaryH1Density)
    {F : ℂ → ℝ} {B : ℝ≥0} (hF : ContDiff ℝ 1 F) (hz : F 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ B)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) :
    HasWeakGradient (fun x => F (u x)) (fun x =>
      (fderiv ℝ F (u x) 1) • U x+(fderiv ℝ F (u x) Complex.I) • V x) := by
  let P : ℝ × ℝ → ℝ := fun z => F (Complex.equivRealProdCLM.symm z)
  let a : ℝ × ℝ → ℝ := fun z => fderiv ℝ F (Complex.equivRealProdCLM.symm z) 1
  let b : ℝ × ℝ → ℝ := fun z => fderiv ℝ F (Complex.equivRealProdCLM.symm z) Complex.I
  have hdiff := hF.differentiable (by simp)
  have hc := hF.continuous_fderiv (by simp)
  have hLip : LipschitzWith B F := lipschitzWith_of_nnnorm_fderiv_le hdiff
    (fun z => NNReal.coe_le_coe.mp (hbound z))
  have ha : Continuous a := (hc.comp Complex.equivRealProdCLM.symm.continuous).clm_apply continuous_const
  have hb : Continuous b := (hc.comp Complex.equivRealProdCLM.symm.continuous).clm_apply continuous_const
  have hab (z : ℝ × ℝ) : ‖a z‖ ≤ (B : ℝ) := by
    exact ((fderiv ℝ F _).le_opNorm 1).trans (by simpa using hbound (Complex.equivRealProdCLM.symm z))
  have hbb (z : ℝ × ℝ) : ‖b z‖ ≤ (B : ℝ) := by
    exact ((fderiv ℝ F _).le_opNorm Complex.I).trans
      (by simpa using hbound (Complex.equivRealProdCLM.symm z))
  have hd (z w : ℝ × ℝ) : fderiv ℝ P z w = a z*w.1+b z*w.2 := by
    have hcomp := (hdiff (Complex.equivRealProdCLM.symm z)).hasFDerivAt.comp z
      (Complex.equivRealProdCLM.symm.hasFDerivAt)
    change fderiv ℝ (F ∘ Complex.equivRealProdCLM.symm) z w = _
    rw [hcomp.fderiv]
    exact realCLM_apply_pair _ w
  have hh := hasWeakGradient_bounded_pair_comp_dotH1 hDensity
    (hdiff.comp Complex.equivRealProdCLM.symm.differentiable)
    (hLip.comp Complex.equivRealProdCLM.symm.toContinuousLinearMap.lipschitzWith)
    (by simpa using hz) ha hb hab hbb hd hu
  simpa only [a,b,Complex.equivRealProdCLM_symm_apply_re,
    Complex.equivRealProdCLM_symm_apply_im, Complex.equivRealProdCLM_symm_apply, Function.comp_def, Complex.re_add_im] using hh

#print axioms realCLM_apply_pair
#print axioms hasWeakGradient_bounded_complex_comp_dotH1
end HartreeF.WeakHartreeChain
