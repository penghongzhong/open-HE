import WeakPairChainRule
import CutoffGeometry

/-! Native bounded-C1 composition for the genuine homogeneous H1 domain.
Spatial localization supplies L2; the original field is assumed only L6. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace NNReal ENNReal Topology
namespace HartreeF.WeakHartreeChain
open SobolevStretch ModulusGradient CutoffApproximation StationarySelfTest

theorem hasWeakGradient_of_local_agreement
    {u : Space → ℝ} {G : Space → Space}
    (hu : LocallyIntegrable u volume) (hG : LocallyIntegrable G volume)
    (hloc : ∀ n : ℕ, ∃ un : Space → ℝ, ∃ Gn : Space → Space,
      HasWeakGradient un Gn ∧ ∀ x, ‖x‖ ≤ n → un x = u x ∧ Gn x = G x) :
    HasWeakGradient u G := by
  refine ⟨hu, hG, ?_⟩
  intro v φ hφ hc
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : Space)
  obtain ⟨n, hn⟩ := exists_nat_gt R
  obtain ⟨un, Gn, hw, heq⟩ := hloc n
  have hball (x : Space) (hx : x ∈ tsupport φ) : ‖x‖ ≤ n :=
    (show ‖x‖ ≤ R from by simpa using hR hx).trans hn.le
  have hleft : (fun x => un x*fderiv ℝ φ x v) = (fun x => u x*fderiv ℝ φ x v) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [(heq x (hball x hx)).1]
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  have hright : (fun x => ⟪Gn x,v⟫*φ x) = (fun x => ⟪G x,v⟫*φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [(heq x (hball x hx)).2]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  simpa only [← hleft, ← hright] using hw.integration_by_parts v φ hφ hc

theorem hasWeakGradient_bounded_pair_comp_dotH1 (hDensity : OrdinaryH1Density)
    {F a b : ℝ × ℝ → ℝ} {K : ℝ≥0} {B : ℝ}
    (hF : Differentiable ℝ F) (hLip : LipschitzWith K F) (hzero : F 0 = 0)
    (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ z, ‖a z‖ ≤ B) (hbb : ∀ z, ‖b z‖ ≤ B)
    (hd : ∀ z w, fderiv ℝ F z w = a z*w.1+b z*w.2)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V) :
    HasWeakGradient (fun x => F ((u x).re, (u x).im))
      (fun x => a ((u x).re,(u x).im) • U x+b ((u x).re,(u x).im) • V x) := by
  have hr := hu.function_L6.continuousLinearMap_comp Complex.reCLM
  have hi := hu.function_L6.continuousLinearMap_comp Complex.imCLM
  have hp : MemLp (fun x => ((u x).re,(u x).im)) 6 volume := memLp_prod_iff.mpr ⟨hr,hi⟩
  have hca := continuous_bounded_coefficient_memLp hr.aestronglyMeasurable
    hi.aestronglyMeasurable ha hab hu.real_gradient_L2
  have hcb := continuous_bounded_coefficient_memLp hr.aestronglyMeasurable
    hi.aestronglyMeasurable hb hbb hu.imag_gradient_L2
  apply hasWeakGradient_of_local_agreement
    ((hLip.comp_memLp hzero hp).locallyIntegrable (by norm_num))
    ((hca.add hcb).locallyIntegrable (by norm_num))
  intro n
  obtain ⟨hl2,hcut⟩ := CutoffApproximation.cutoff_L2_and_dotH1 hu n
  have hre := hl2.continuousLinearMap_comp Complex.reCLM
  have him := hl2.continuousLinearMap_comp Complex.imCLM
  have hw := hasWeakGradient_pair_comp hDensity hF hLip hzero ha hb hab hbb hd
    hre him hcut.real_gradient_L2 hcut.imag_gradient_L2 hcut.real_weak hcut.imag_weak
  refine ⟨_,_,hw,?_⟩
  intro x hx
  have hc := cutoff_eq_one n (x := x) (by linarith)
  have hg := cutoff_gradient_zero n hx
  simp only [hc, hg, one_smul, smul_zero, add_zero]
  exact ⟨rfl,rfl⟩

#print axioms hasWeakGradient_of_local_agreement
#print axioms hasWeakGradient_bounded_pair_comp_dotH1
end HartreeF.WeakHartreeChain
