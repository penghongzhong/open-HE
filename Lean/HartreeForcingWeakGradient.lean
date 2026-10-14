import HartreeWeakProductLimit

/-! The actual real and imaginary weak gradients of the full Hartree forcing.
The product identity is produced from ordinary H1 density and Sobolev, actual
Riesz weak commutation, and dominated cutoff removal. It is not an input. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeProduct
open ForcingDomain RieszWeakDerivative WeakHartreeChain SobolevStretch StationarySelfTest

def forcingGradientRe (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  potentialProductGradient α c (projectedLocalFactor (1+α) Complex.reCLM) u U V

def forcingGradientIm (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  potentialProductGradient α c (projectedLocalFactor (1+α) Complex.imCLM) u U V

theorem complexChainGradient_projectedLocalFactor {q : ℝ} (hq : 1 < q)
    (L : ℂ →L[ℝ] ℝ) (u : Space → ℂ) (U V : Space → Space) :
    complexChainGradient (projectedLocalFactor q L) u U V = projectedLocalFactorGradient q L u U V := by
  funext x
  simp only [complexChainGradient,projectedLocalFactorGradient,projectedLocalFactor_fderiv hq,
    ContinuousLinearMap.comp_apply]

theorem projected_forcing_hasWeakGradient (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => L (forcing α c u x))
      (potentialProductGradient α c (projectedLocalFactor (1+α) L) u U V) := by
  have hw := projected_product_hasWeakGradient hDensity hSob hH L hL hu hu10 hU hV
  convert hw using 1
  funext x
  change L (potential α c u x • ForcingDomain.localFactor α u x) =
    potential α c u x*L (WeakHartreeChain.localFactor (1+α) (u x))
  rw [map_smul,smul_eq_mul]
  rfl

theorem forcingGradientRe_formula {α : ℝ} (hα : 0 < α) (c : ℝ)
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    forcingGradientRe α c u U V x =
      (ForcingDomain.localFactor α u x).re • hartreePotentialGradient α c u U V x+
        potential α c u x • localFactorGradientRe (1+α) u U V x := by
  unfold forcingGradientRe potentialProductGradient
  rw [complexChainGradient_projectedLocalFactor (by linarith : 1 < 1+α),projectedLocalFactorGradient_re]
  rfl

theorem forcingGradientIm_formula {α : ℝ} (hα : 0 < α) (c : ℝ)
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    forcingGradientIm α c u U V x =
      (ForcingDomain.localFactor α u x).im • hartreePotentialGradient α c u U V x+
        potential α c u x • localFactorGradientIm (1+α) u U V x := by
  unfold forcingGradientIm potentialProductGradient
  rw [complexChainGradient_projectedLocalFactor (by linarith : 1 < 1+α),projectedLocalFactorGradient_im]
  rfl

theorem hartree_forcing_weak_gradients (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => (forcing α c u x).re) (forcingGradientRe α c u U V) ∧
    HasWeakGradient (fun x => (forcing α c u x).im) (forcingGradientIm α c u U V) :=
  ⟨projected_forcing_hasWeakGradient hDensity hSob hH Complex.reCLM reCLM_norm_le_one hu hu10 hU hV,
    projected_forcing_hasWeakGradient hDensity hSob hH Complex.imCLM imCLM_norm_le_one hu hu10 hU hV⟩

theorem hartree_forcing_gradient_domains {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (forcingGradientRe α c u U V) (ENNReal.ofReal (6/5 : ℝ)) volume ∧
    MemLp (forcingGradientIm α c u U V) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  have hr := localFactor_growth_bounds hH.order_pos Complex.reCLM reCLM_norm_le_one
  have hi := localFactor_growth_bounds hH.order_pos Complex.imCLM imCLM_norm_le_one
  exact ⟨potentialProductGradient_memLp hH (projectedLocalFactor_contDiff_one (by linarith [hH.order_pos]) _) hr.1 hr.2 hu6 hu10 hU hV,
    potentialProductGradient_memLp hH (projectedLocalFactor_contDiff_one (by linarith [hH.order_pos]) _) hi.1 hi.2 hu6 hu10 hU hV⟩

#print axioms complexChainGradient_projectedLocalFactor
#print axioms projected_forcing_hasWeakGradient
#print axioms forcingGradientRe_formula
#print axioms forcingGradientIm_formula
#print axioms hartree_forcing_weak_gradients
#print axioms hartree_forcing_gradient_domains
end HartreeF.WeakHartreeProduct
