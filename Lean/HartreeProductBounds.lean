import HartreeProductMajorantDomains
import BoundedCompositionH1Domains

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeakHartreeProduct
open ForcingDomain RieszWeakDerivative WeakHartreeChain

def potentialProduct (α c : ℝ) (F : ℂ → ℝ) (u : Space → ℂ) (x : Space) : ℝ :=
  potential α c u x*F (u x)

def potentialProductGradient (α c : ℝ) (F : ℂ → ℝ) (u : Space → ℂ)
    (U V : Space → Space) (x : Space) : Space :=
  F (u x) • hartreePotentialGradient α c u U V x+potential α c u x • complexChainGradient F u U V x

def gradientMagnitude (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) (x : Space) : ℝ :=
  fourthGradientMagnitude α c u U V x+(3*(2+α))*firstGradientMagnitude α c u U V x

theorem potentialProduct_norm_bound {α c : ℝ} {F : ℂ → ℝ}
    (hfb : ∀ z, ‖F z‖ ≤ ‖z‖^(2+α)) (u : Space → ℂ) (x : Space) :
    ‖potentialProduct α c F u x‖ ≤ forcingMagnitude α c u x := by
  rw [potentialProduct,norm_mul]
  exact mul_le_mul_of_nonneg_left (hfb (u x)) (norm_nonneg _)

theorem potentialProductGradient_norm_bound {α c : ℝ} {F : ℂ → ℝ}
    (hfb : ∀ z, ‖F z‖ ≤ ‖z‖^(2+α))
    (hdb : ∀ z, ‖fderiv ℝ F z‖ ≤ (3*(2+α))*‖z‖^(1+α))
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    ‖potentialProductGradient α c F u U V x‖ ≤ gradientMagnitude α c u U V x := by
  calc
    _ ≤ ‖F (u x) • hartreePotentialGradient α c u U V x‖+
        ‖potential α c u x • complexChainGradient F u U V x‖ := norm_add_le _ _
    _ ≤ ‖u x‖^(2+α)*‖hartreePotentialGradient α c u U V x‖+
        ‖potential α c u x‖*((3*(2+α))*powerGradientMajorant (1+α) u U V x) := by
      rw [norm_smul,norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_right (hfb _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (complexChainGradient_bound hdb u U V x) (norm_nonneg _))
    _ = _ := by unfold gradientMagnitude fourthGradientMagnitude firstGradientMagnitude powerGradientMajorant; ring

theorem gradientMagnitude_nonneg {α : ℝ} (hα : 0 < α) (c : ℝ)
    (u : Space → ℂ) (U V : Space → Space) (x : Space) : 0 ≤ gradientMagnitude α c u U V x := by
  have h := product_magnitudes_nonneg α c u U V x
  exact add_nonneg h.2.2 (mul_nonneg (by positivity) h.2.1)

theorem gradientMagnitude_memLp {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (gradientMagnitude α c u U V) (ENNReal.ofReal (6/5 : ℝ)) volume :=
  (fourthGradientMagnitude_memLp hH hu6 hu10 hU hV).add
    ((firstGradientMagnitude_memLp hH hu6 hu10 hU hV).const_mul (3*(2+α)))

theorem potentialProduct_aestronglyMeasurable {α c : ℝ} (hH : OrdinaryHLS α c)
    {F : ℂ → ℝ} (hF : Continuous F) {u : Space → ℂ}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume) :
    AEStronglyMeasurable (potentialProduct α c F u) volume :=
  (hartreePotential_memLp_split hH hu6 hu10).aestronglyMeasurable.mul
    (hF.comp_aestronglyMeasurable hu6.aestronglyMeasurable)

theorem potentialProductGradient_aestronglyMeasurable {α c : ℝ} (hH : OrdinaryHLS α c)
    {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F) {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    AEStronglyMeasurable (potentialProductGradient α c F u U V) volume :=
  ((hF.continuous.comp_aestronglyMeasurable hu6.aestronglyMeasurable).smul
    (hartreePotentialGradient_domain hH hu6 hu10 hU hV).2.aestronglyMeasurable).add
    ((hartreePotential_memLp_split hH hu6 hu10).aestronglyMeasurable.smul
      (complexChainGradient_aestronglyMeasurable hF hu6.aestronglyMeasurable hU.aestronglyMeasurable hV.aestronglyMeasurable))

theorem potentialProduct_memLp {α c : ℝ} (hH : OrdinaryHLS α c)
    {F : ℂ → ℝ} (hF : Continuous F) (hfb : ∀ z, ‖F z‖ ≤ ‖z‖^(2+α))
    {u : Space → ℂ} (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume) :
    MemLp (potentialProduct α c F u) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  apply (forcingMagnitude_memLp hH hu6).of_le (potentialProduct_aestronglyMeasurable hH hF hu6 hu10)
  filter_upwards [] with x
  exact (potentialProduct_norm_bound hfb u x).trans (le_abs_self _)

theorem potentialProductGradient_memLp {α c : ℝ} (hH : OrdinaryHLS α c)
    {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F) (hfb : ∀ z, ‖F z‖ ≤ ‖z‖^(2+α))
    (hdb : ∀ z, ‖fderiv ℝ F z‖ ≤ (3*(2+α))*‖z‖^(1+α))
    {u : Space → ℂ} {U V : Space → Space}
    (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (potentialProductGradient α c F u U V) (ENNReal.ofReal (6/5 : ℝ)) volume := by
  apply (gradientMagnitude_memLp hH hu6 hu10 hU hV).of_le
    (potentialProductGradient_aestronglyMeasurable hH hF hu6 hu10 hU hV)
  filter_upwards [] with x
  exact (potentialProductGradient_norm_bound hfb hdb u U V x).trans (le_abs_self _)

#print axioms potentialProduct_norm_bound
#print axioms potentialProductGradient_norm_bound
#print axioms gradientMagnitude_nonneg
#print axioms gradientMagnitude_memLp
#print axioms potentialProduct_aestronglyMeasurable
#print axioms potentialProductGradient_aestronglyMeasurable
#print axioms potentialProduct_memLp
#print axioms potentialProductGradient_memLp
end HartreeF.WeakHartreeProduct
