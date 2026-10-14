import HartreeForcingWeakGradient

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.WeakHartreeProduct
open ForcingDomain RieszWeakDerivative WeakHartreeChain GradientMajorants

def directionalField (U V : Space → Space) (v x : Space) : ℂ :=
  Complex.equivRealProdCLM.symm (⟪U x,v⟫,⟪V x,v⟫)

theorem directionalField_memLp {p : ℝ≥0∞} {U V : Space → Space}
    (hU : MemLp U p volume) (hV : MemLp V p volume) (v : Space) :
    MemLp (directionalField U V v) p volume := by
  have hUr : MemLp (fun x => ⟪U x,v⟫) p volume := by
    simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm v] using (innerSL ℝ v).comp_memLp' hU
  have hVr : MemLp (fun x => ⟪V x,v⟫) p volume := by
    simpa only [Function.comp_def,innerSL_apply_apply,real_inner_comm v] using (innerSL ℝ v).comp_memLp' hV
  exact Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp_memLp'
    (memLp_prod_iff.mpr ⟨hUr,hVr⟩)

theorem densityGradient_directional (p : ℝ) (u : Space → ℂ) (U V : Space → Space) (v x : Space) :
    ⟪densityGradient p u U V x,v⟫ = densityDerivative p (u x) (directionalField U V v x) := by
  simp only [densityGradient,densityDerivative_apply,inner_add_left,real_inner_smul_left,
    directionalField,Complex.equivRealProdCLM_symm_apply_re,Complex.equivRealProdCLM_symm_apply_im,
    Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_add,add_zero]
  ring

theorem projectedChainGradient_directional {q : ℝ} (hq : 1 < q) (L : ℂ →L[ℝ] ℝ)
    (u : Space → ℂ) (U V : Space → Space) (v x : Space) :
    ⟪complexChainGradient (projectedLocalFactor q L) u U V x,v⟫ =
      L (localFactorDerivative q (u x) (directionalField U V v x)) := by
  simp only [complexChainGradient,projectedLocalFactor_fderiv hq,ContinuousLinearMap.comp_apply,
    inner_add_left,real_inner_smul_left]
  exact (realCLM_apply_pair (L.comp (localFactorDerivative q (u x))) (⟪U x,v⟫,⟪V x,v⟫)).symm

theorem projectedProductGradient_directional {α : ℝ} (hα : 0 < α) (c : ℝ)
    (L : ℂ →L[ℝ] ℝ) (u : Space → ℂ) (U V : Space → Space) (v x : Space) :
    ⟪potentialProductGradient α c (projectedLocalFactor (1+α) L) u U V x,v⟫ =
      L (⟪hartreePotentialGradient α c u U V x,v⟫ • WeakHartreeChain.localFactor (1+α) (u x)+
        potential α c u x • localFactorDerivative (1+α) (u x) (directionalField U V v x)) := by
  rw [potentialProductGradient,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    projectedChainGradient_directional (by linarith : 1 < 1+α)]
  simp only [map_add,map_smul,smul_eq_mul,projectedLocalFactor,Function.comp_def]
  ring

theorem forcingGradient_directional_complex {α : ℝ} (hα : 0 < α) (c : ℝ)
    (u : Space → ℂ) (U V : Space → Space) (v x : Space) :
    directionalField (forcingGradientRe α c u U V) (forcingGradientIm α c u U V) v x =
      ⟪hartreePotentialGradient α c u U V x,v⟫ • WeakHartreeChain.localFactor (1+α) (u x)+
        potential α c u x • localFactorDerivative (1+α) (u x) (directionalField U V v x) := by
  apply Complex.ext
  · exact projectedProductGradient_directional hα c Complex.reCLM u U V v x
  · exact projectedProductGradient_directional hα c Complex.imCLM u U V v x

theorem forcingGradient_directional_ae {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) (v : Space) :
    directionalField (forcingGradientRe α c u U V) (forcingGradientIm α c u U V) v =ᵐ[volume]
      (fun x => rieszConvolution α c (fun y => densityDerivative (3+α) (u y) (directionalField U V v y)) x •
        WeakHartreeChain.localFactor (1+α) (u x)+
        potential α c u x • localFactorDerivative (1+α) (u x) (directionalField U V v x)) := by
  have hr := gradient_hls_ranges hH.order_pos hH.order_lt_three
  have hi := rieszVectorConvolution_inner hH hr.2.2.1 hr.2.2.2
    (hartreeDensityGradient_split_memLp hH.order_pos hH.order_lt_three hu6 hu10 hU hV) v
  have he : (fun y => ⟪hartreeDensityGradient α u U V y,v⟫) =
      (fun y => densityDerivative (3+α) (u y) (directionalField U V v y)) := by
    funext y
    rw [hartreeDensityGradient_eq]
    exact densityGradient_directional (3+α) u U V v y
  rw [he] at hi
  filter_upwards [hi] with x hx
  rw [forcingGradient_directional_complex hH.order_pos c u U V v x]
  change ⟪hartreePotentialGradient α c u U V x,v⟫ = _ at hx
  rw [hx]

#print axioms directionalField_memLp
#print axioms densityGradient_directional
#print axioms projectedChainGradient_directional
#print axioms projectedProductGradient_directional
#print axioms forcingGradient_directional_complex
#print axioms forcingGradient_directional_ae
end HartreeF.WeakHartreeProduct
