import FLowEnergyHartreeL1Gradient
import FLowEnergyHartreeUpperL1Gradient

/-!
UNCOMPILED DRAFT. The extra ordinary HLS hypothesis is guarded by 1 < alpha.
At alpha = 1 the lower-order branch is used and no order-zero HLS is asked
for or consumed. The original independently frozen lower-order sources
remain unmodified.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient
open EnergySpace EnergySpace.Highpass PhysicalLowpass SobolevStretch StationarySelfTest
  ForcingDomain WeakHartreeProduct WeakHartreeChain GradientMajorants YoungSource

/-- All ordinary-HLS orders 0 < alpha < 3, with the extra assumption only
in the genuinely upper-order branch. -/
theorem lowEnergyState_forcing_L1_weakGradients_allOrders
    (hDensity : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c')
    (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    let v := lowEnergyState hDensity hSob q hL u
    let U := energyProjectedGradient Complex.reCLM v
    let V := energyProjectedGradient Complex.imCLM v
    HasWeakGradient (fun x => (forcing α c (energyValue v) x).re)
      (forcingGradientRe α c (energyValue v) U V) ∧
    HasWeakGradient (fun x => (forcing α c (energyValue v) x).im)
      (forcingGradientIm α c (energyValue v) U V) ∧
    MemLp (forcingGradientRe α c (energyValue v) U V) 1 volume ∧
    MemLp (forcingGradientIm α c (energyValue v) U V) 1 volume := by
  by_cases hα1 : α ≤ 1
  · exact lowEnergyState_forcing_L1_weakGradients_smallOrder hDensity hSob hH hα1 q hL u
  · obtain ⟨c', hLowerHLS⟩ := hUpper (lt_of_not_ge hα1)
    exact lowEnergyState_forcing_L1_weakGradients_upperOrder hDensity hSob hH hLowerHLS q hL u

/-- Quantitative all-order pure-gradient bound on the same fixed-cutoff state. -/
theorem lowEnergyState_forcing_L1_gradient_bound_allOrders
    (hDensity : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (L : ℝ) (hL : 0 < L) (u : EnergyState),
      let v := lowEnergyState hDensity hSob q hL u
      let U := energyProjectedGradient Complex.reCLM v
      let V := energyProjectedGradient Complex.imCLM v
      (eLpNorm (forcingGradientRe α c (energyValue v) U V) 1 volume).toReal +
        (eLpNorm (forcingGradientIm α c (energyValue v) U V) 1 volume).toReal ≤
        C * cutoffYoungConstant q * Real.sqrt L * pureGradientNorm u ^ (5 + 2 * α) := by
  by_cases hα1 : α ≤ 1
  · exact lowEnergyState_forcing_L1_gradient_bound_smallOrder hDensity hSob hH hα1
  · obtain ⟨c', hLowerHLS⟩ := hUpper (lt_of_not_ge hα1)
    exact lowEnergyState_forcing_L1_gradient_bound_upperOrder hDensity hSob hH hLowerHLS

/-- Alpha = 1 is an unconditional consumer of only its positive-order HLS. -/
theorem lowEnergyState_forcing_L1_gradient_bound_orderOne
    (hDensity : OrdinaryH1Density) {K c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS 1 c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (L : ℝ) (hL : 0 < L) (u : EnergyState),
      let v := lowEnergyState hDensity hSob q hL u
      let U := energyProjectedGradient Complex.reCLM v
      let V := energyProjectedGradient Complex.imCLM v
      (eLpNorm (forcingGradientRe 1 c (energyValue v) U V) 1 volume).toReal +
        (eLpNorm (forcingGradientIm 1 c (energyValue v) U V) 1 volume).toReal ≤
        C * cutoffYoungConstant q * Real.sqrt L * pureGradientNorm u ^ (7 : ℝ) := by
  simpa only [mul_one, show (5 : ℝ) + 2 = 7 by norm_num] using
    lowEnergyState_forcing_L1_gradient_bound_smallOrder hDensity hSob hH (by norm_num)

#print axioms lowEnergyState_forcing_L1_weakGradients_allOrders
#print axioms lowEnergyState_forcing_L1_gradient_bound_allOrders
#print axioms lowEnergyState_forcing_L1_gradient_bound_orderOne
end HartreeF.BoundedHartreeGradient
