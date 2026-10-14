import HartreePotentialWeakGradient
import StationaryH1Extension

/-! A genuine asymmetric weak Leibniz theorem. One factor has an L2 function
and an L6/5 weak gradient; the other has an L6 function and an L2 weak gradient.
Only the existing ordinary H1 density and ordinary Sobolev inequality are used. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.WeakHartreeProduct
open SobolevStretch StationarySelfTest WeakCutoffLp

theorem weak_leibniz_L2_L65_H1 (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {a b : Space → ℝ} {A B : Space → Space}
    (hwa : HasWeakGradient a A) (hwb : HasWeakGradient b B)
    (ha : MemLp a 2 volume) (hA : MemLp A (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hb : MemLp b 6 volume) (hB : MemLp B 2 volume) :
    HasWeakGradient (fun x => a x*b x) (fun x => b x • A x+a x • B x) := by
  have hh : Real.HolderTriple 2 6 (3/2) := by constructor <;> norm_num
  let : ENNReal.HolderTriple 2 6 (ENNReal.ofReal (3/2 : ℝ)) := by
    simpa only [ENNReal.ofReal_ofNat] using hh.ennrealOfReal
  let := holder_six_fifths_six
  have hab : MemLp (fun x => a x*b x) (ENNReal.ofReal (3/2 : ℝ)) volume := ha.mul hb
  have haB : MemLp (fun x => a x • B x) 1 volume := ha.smul hB
  have hbA : MemLp (fun x => b x • A x) 1 volume := hb.smul hA
  have habloc := hab.locallyIntegrable (by norm_num : 1 ≤ ENNReal.ofReal (3/2 : ℝ))
  have haBloc := haB.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have hbAloc := hbA.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  refine ⟨habloc,hbAloc.add haBloc,?_⟩
  intro v φ hφ hc
  have hav : MemLp (fun x => a x • v) 2 volume :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight v).comp_memLp' ha
  have hAv : MemLp (fun x => -⟪A x,v⟫) (ENNReal.ofReal (6/5 : ℝ)) volume := by
    have hm : MemLp (fun x => ⟪A x,v⟫) (ENNReal.ofReal (6/5 : ℝ)) volume := by
      simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm v] using (innerSL ℝ v).comp_memLp' hA
    convert! hm.neg using 1
  have heq : ∀ ψ : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, ⟪a x • v,gradient ψ x⟫) = ∫ x, (-⟪A x,v⟫)*ψ x := by
    intro ψ hψ hcψ
    have he (x : Space) : ⟪a x • v,gradient ψ x⟫ = a x*fderiv ℝ ψ x v := by
      rw [real_inner_smul_left,real_inner_comm (gradient ψ x) v,inner_gradient_left]
    simp_rw [he,neg_mul,integral_neg]
    exact hwa.integration_by_parts v ψ hψ hcψ
  have hφb2 := cutoff_smul_memLp_two hφ.continuous hc hb
  have hφb6 := cutoff_smul_memLp hφ.continuous hc hb
  have hφB := (cutoff_gradient_field_memLp_two hφ.continuous hc hB).add
    (function_smul_cutoff_gradient_memLp_two hφ hc hb)
  have hex := weak_equation_extend_h1 hDensity hSob hav hAv heq
    hφb2 hφb6 hφB (hwb.mul_smooth hφ)
  have hiA : Integrable (fun x => a x*⟪B x,v⟫*φ x) volume := by
    simpa only [real_inner_smul_left] using (weak_test_integrable habloc haBloc hφ hc v).2
  have hiB : Integrable (fun x => a x*b x*fderiv ℝ φ x v) volume :=
    (weak_test_integrable habloc haBloc hφ hc v).1
  have hiC : Integrable (fun x => b x*⟪A x,v⟫*φ x) volume := by
    simpa only [real_inner_smul_left] using (weak_test_integrable habloc hbAloc hφ hc v).2
  have hleft : (fun x => ⟪a x • v,φ x • B x+b x • gradient φ x⟫) =
      (fun x => a x*⟪B x,v⟫*φ x+a x*b x*fderiv ℝ φ x v) := by
    funext x
    rw [real_inner_smul_left,inner_add_right,inner_smul_right,inner_smul_right,
      real_inner_comm (gradient φ x) v,inner_gradient_left,real_inner_comm (B x) v]
    ring
  have hright : (fun x => (-⟪A x,v⟫)*(φ x*b x)) =
      (fun x => -(b x*⟪A x,v⟫*φ x)) := by funext x; ring
  change (∫ x, ⟪a x • v,φ x • B x+b x • gradient φ x⟫) =
    ∫ x, (-⟪A x,v⟫)*(φ x*b x) at hex
  rw [hleft,integral_add hiA hiB,hright,integral_neg] at hex
  have hout : (fun x => ⟪b x • A x+a x • B x,v⟫*φ x) =
      (fun x => b x*⟪A x,v⟫*φ x+a x*⟪B x,v⟫*φ x) := by
    funext x
    simp only [inner_add_left,real_inner_smul_left,add_mul]
  rw [hout,integral_add hiC hiA]
  linarith

#print axioms weak_leibniz_L2_L65_H1
end HartreeF.WeakHartreeProduct
