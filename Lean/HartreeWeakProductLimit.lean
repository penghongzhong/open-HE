import CutoffHartreeProducts

/-! Removal of amplitude and spatial cutoffs in the genuine weak product.
All dominating function/gradient products have actual critical L6/5 domains. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.WeakHartreeProduct
open ForcingDomain RieszWeakDerivative WeakHartreeChain SobolevStretch StationarySelfTest CutoffApproximation

theorem cutoff_projected_product_hasWeakGradient (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume)
    {χ : Space → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    HasWeakGradient (cutoffPotentialProduct α c (projectedLocalFactor (1+α) L) u χ)
      (cutoffPotentialProductGradient α c (projectedLocalFactor (1+α) L) u U V χ) := by
  let F := projectedLocalFactor (1+α) L
  let Fn : ℕ → ℂ → ℝ := fun n => retractedMap F (saturationParameter n)
  have hF : ContDiff ℝ 1 F := projectedLocalFactor_contDiff_one (by linarith [hH.order_pos]) L
  have hb := localFactor_growth_bounds hH.order_pos L hL
  have htarget := cutoff_product_domains hH hF hb.1 hb.2 hu.function_L6 hu10 hU hV hχ hc
  have hdom := cutoff_product_magnitude_domains hH hu.function_L6 hu10 hU hV hχ hc
  apply hasWeakGradient_of_locally_dominated_limit
    (fn := fun n => cutoffPotentialProduct α c (Fn n) u χ)
    (Gn := fun n => cutoffPotentialProductGradient α c (Fn n) u U V χ)
    (M := cutoffFunctionMagnitude α c u χ) (N := cutoffGradientMagnitude α c u U V χ)
    (htarget.1.locallyIntegrable (by norm_num)) (htarget.2.locallyIntegrable (by norm_num))
    (hdom.1.locallyIntegrable (by norm_num)) (hdom.2.locallyIntegrable (by norm_num))
    (fun n => cutoff_retracted_product_hasWeakGradient hDensity hSob hH L hL hu hu10 hU hV hχ hc n)
  · intro n
    have hbnd := retracted_localFactor_growth_bounds hH.order_pos L hL n
    exact ae_of_all _ (fun x => (cutoff_product_bounds hbnd.1 hbnd.2 u U V χ x).1)
  · intro n
    have hbnd := retracted_localFactor_growth_bounds hH.order_pos L hL n
    exact ae_of_all _ (fun x => (cutoff_product_bounds hbnd.1 hbnd.2 u U V χ x).2)
  · filter_upwards [] with x
    exact (tendsto_const_nhds (x := χ x)).mul
      ((tendsto_const_nhds (x := potential α c u x)).mul (retractedMap_tendsto hF.continuous (u x)))
  · filter_upwards [] with x
    have hf := retractedMap_tendsto hF.continuous (u x)
    have hg := complexChainGradient_tendsto (retractedMap_fderiv_tendsto hF) u U V x
    have hbase := (hf.smul (tendsto_const_nhds (x := hartreePotentialGradient α c u U V x))).add
      ((tendsto_const_nhds (x := potential α c u x)).smul hg)
    exact ((tendsto_const_nhds (x := χ x)).smul hbase).add
      (((tendsto_const_nhds (x := potential α c u x)).mul hf).smul
        (tendsto_const_nhds (x := gradient χ x)))

theorem projected_product_hasWeakGradient (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (potentialProduct α c (projectedLocalFactor (1+α) L) u)
      (potentialProductGradient α c (projectedLocalFactor (1+α) L) u U V) := by
  have hF := projectedLocalFactor_contDiff_one (by linarith [hH.order_pos] : 1 < 1+α) L
  have hb := localFactor_growth_bounds hH.order_pos L hL
  have hf := potentialProduct_memLp hH hF.continuous hb.1 hu.function_L6 hu10
  have hg := potentialProductGradient_memLp hH hF hb.1 hb.2 hu.function_L6 hu10 hU hV
  apply hasWeakGradient_of_local_agreement (hf.locallyIntegrable (by norm_num)) (hg.locallyIntegrable (by norm_num))
  intro k
  refine ⟨_,_,cutoff_projected_product_hasWeakGradient hDensity hSob hH L hL hu hu10 hU hV
    (cutoff_smooth k) (cutoff_compact k),?_⟩
  intro x hx
  have hχ := cutoff_eq_one k (x := x) (by linarith)
  have hdχ := cutoff_gradient_zero k hx
  simp only [cutoffPotentialProduct,cutoffPotentialProductGradient,hχ,hdχ,one_mul,one_smul,smul_zero,add_zero,and_self]

#print axioms cutoff_projected_product_hasWeakGradient
#print axioms projected_product_hasWeakGradient
end HartreeF.WeakHartreeProduct
