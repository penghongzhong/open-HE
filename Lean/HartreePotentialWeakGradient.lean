import RieszWeakGradient

/-! Actual weak derivative of the Hartree potential, all 0<alpha<3. This is
convolution differentiation, not the still-separate weak product with the local factor. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.RieszWeakDerivative
open ForcingDomain GradientMajorants SobolevStretch StationarySelfTest WeakHartreeChain

def hartreePotentialGradient (α c : ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  rieszVectorConvolution α c (hartreeDensityGradient α u U V)

theorem hartree_potential_hasWeakGradient (hDensity : OrdinaryH1Density)
    {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (potential α c u) (hartreePotentialGradient α c u U V) := by
  have hr := gradient_hls_ranges hH.order_pos hH.order_lt_three
  have hfd := first_density_bound hH.order_pos hH.order_lt_three
    (fun x => norm_nonneg (u x)) hu.function_L6.norm hu10.norm
  have hgd := hartreeDensityGradient_split_memLp hH.order_pos hH.order_lt_three hu.function_L6 hu10 hU hV
  rw [potential_eq_convolution]
  exact riesz_hasWeakGradient hH hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    (hartree_density_hasWeakGradient hDensity hH.order_pos hH.order_lt_three hu hu10 hU hV)
    hfd.memLp hgd

theorem hartreePotentialGradient_domain {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : Space → ℂ} {U V : Space → Space} (hu6 : MemLp u 6 volume)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y) • hartreeDensityGradient α u U V y) volume) ∧
    MemLp (hartreePotentialGradient α c u U V)
      (ENNReal.ofReal (1/(reciprocalB α-α/3))) volume := by
  have hr := gradient_hls_ranges hH.order_pos hH.order_lt_three
  exact rieszVectorConvolution_domain hH hr.2.2.1 hr.2.2.2
    (hartreeDensityGradient_split_memLp hH.order_pos hH.order_lt_three hu6 hu10 hU hV)

#print axioms hartree_potential_hasWeakGradient
#print axioms hartreePotentialGradient_domain
end HartreeF.RieszWeakDerivative
