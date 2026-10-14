import FHartreeMapOutputRestart
import FHartreeSubintervalFixedPoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
namespace HartreeF.CriticalPathRestriction
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- Restriction commutes with the actual Hartree map when its initial datum is
its whole-interval output at the new left endpoint. The source remains the
restricted original input; this assertion assumes no fixed point. -/
theorem restrictPath_hartreeDuhamelMap (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b c d : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b)) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd
      (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH
        (hac.trans (hcd.trans hdb)) u0 u) ⟨c, hac, hcd.trans hdb⟩)
      (restrictPath hac hcd hdb u) =
    restrictPath hac hcd hdb (hartreeDuhamelMap hDensity hSob h0 hfree hret hH
      (hac.trans (hcd.trans hdb)) u0 u) := by
  let w := hartreeDuhamelMap hDensity hSob h0 hfree hret hH
    (hac.trans (hcd.trans hdb)) u0 u
  apply energyPath_injective (intervalMeasure c d)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  ext φ
  have hnew := hartreeDuhamelMap_forward_formula hDensity hSob h0 hfree hret hH
    hcd (energyPath _ w ⟨c, hac, hcd.trans hdb⟩) (restrictPath hac hcd hdb u) t φ
  have hold := hartreeDuhamelMap_output_restart_literal hDensity hSob h0 hfree hret hH
    (hac.trans (hcd.trans hdb)) u0 u ⟨c, hac, hcd.trans hdb⟩
    (intervalInclusion hac hdb t) t.property.1 φ
  have hint : (∫ s in Set.Ioc c (t : ℝ), ∫ x,
      (freeTest ((t : ℝ)-s) φ) x • forcing alpha kernel (energyValue
        (extendEnergyPath hcd (energyPath _ (restrictPath hac hcd hdb u)) s)) x) =
    ∫ s in Set.Ioc c (t : ℝ), ∫ x,
      (freeTest ((t : ℝ)-s) φ) x • forcing alpha kernel (energyValue
        (extendEnergyPath (hac.trans (hcd.trans hdb)) (energyPath _ u) s)) x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact congrArg (fun v : EnergyState => ∫ x,
      (freeTest ((t : ℝ)-s) φ) x • forcing alpha kernel (energyValue v) x)
      (extend_restrictPath_eq hac hcd hdb u ⟨hs.1.le, hs.2.trans t.property.2⟩)
  exact hnew.trans ((congrArg
    (fun z : ℂ => FreeFlow.free ((t : ℝ)-c)
      (energyDistribution (energyPath _ w ⟨c, hac, hcd.trans hdb⟩)) φ + Complex.I*z)
    hint).trans (hold.symm.trans
      (congrArg (fun v : EnergyState => energyDistribution v φ)
        (restrictPath_energy hac hcd hdb w t).symm)))

end HartreeF.CriticalPathRestriction
