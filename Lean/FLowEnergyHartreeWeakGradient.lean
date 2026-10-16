import FLpTopInterpolation
import FPhysicalLowpassWeakGradient
import HartreeForcingWeakGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient
open EnergySpace EnergySpace.Highpass PhysicalLowpass SobolevStretch StationarySelfTest
  ForcingDomain WeakHartreeProduct

theorem lowEnergyState_memLp_ten (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    MemLp (energyValue (lowEnergyState hDensity hSob q hL u) : V → ℂ) 10 volume := by
  have h := memLp_of_memLp_and_top (p := 6) (q := 10) (by norm_num) (by norm_num)
    (by simpa using Lp.memLp (energyValue (lowEnergyState hDensity hSob q hL u)))
    (lowEnergyState_memLp_top hDensity hSob q hL u)
  simpa using h

theorem lowEnergyState_projectedGradient_memLp_thirty_thirteen
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (A : ℂ →L[ℝ] ℝ) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    MemLp (energyProjectedGradient A (lowEnergyState hDensity hSob q hL u))
      (ENNReal.ofReal (30 / 13 : ℝ)) volume := by
  exact memLp_of_memLp_and_top (p := 2) (q := 30 / 13) (by norm_num) (by norm_num)
    (by simpa using energyProjectedGradient_memLp A (lowEnergyState hDensity hSob q hL u))
    (lowEnergyState_projectedGradient_memLp_top hDensity hSob A q hL u)

/-- The previous forcing gradient identities now apply to the SAME actual low-state,
with their extra L10 and L(30/13) domain inputs genuinely produced. -/
theorem lowEnergyState_forcing_hasWeakGradients (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {α c : ℝ} (hH : OrdinaryHLS α c)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    let v := lowEnergyState hDensity hSob q hL u
    HasWeakGradient (fun x => (forcing α c (energyValue v) x).re)
      (forcingGradientRe α c (energyValue v)
        (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)) ∧
    HasWeakGradient (fun x => (forcing α c (energyValue v) x).im)
      (forcingGradientIm α c (energyValue v)
        (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)) := by
  exact hartree_forcing_weak_gradients hDensity hSob hH
    (energyState_inDotH1 (lowEnergyState hDensity hSob q hL u))
    (lowEnergyState_memLp_ten hDensity hSob q hL u)
    (lowEnergyState_projectedGradient_memLp_thirty_thirteen hDensity hSob Complex.reCLM q hL u)
    (lowEnergyState_projectedGradient_memLp_thirty_thirteen hDensity hSob Complex.imCLM q hL u)

end HartreeF.BoundedHartreeGradient
