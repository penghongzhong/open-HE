import FHartreeRestartFormula
import FCriticalPathRestriction

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

/-- On the smaller interval, the extended restricted trajectory is exactly the
same canonical energy state as the original trajectory. -/
theorem extend_restrictPath_eq {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u : CriticalPath (intervalMeasure a b)) {s : ℝ} (hs : s ∈ Set.Icc c d) :
    extendEnergyPath hcd (energyPath _ (restrictPath hac hcd hdb u)) s =
      extendEnergyPath (hac.trans (hcd.trans hdb)) (energyPath _ u) s := by
  let ts : Set.Icc c d := ⟨s, hs⟩
  have hnew := extendEnergyPath_val hcd
    (energyPath _ (restrictPath hac hcd hdb u)) ts
  have hold := extendEnergyPath_val (hac.trans (hcd.trans hdb))
    (energyPath _ u) (intervalInclusion hac hdb ts)
  exact hnew.trans ((restrictPath_energy hac hcd hdb u ts).trans hold.symm)

/-- Restricting a literal Hartree fixed point gives a literal fixed point of
the actual map restarted with that solution's value at the new left endpoint. -/
theorem restrictPath_hartree_fixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b c d : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH
      (hac.trans (hcd.trans hdb)) u0 u = u) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcd
      (energyPath _ u ⟨c, hac, hcd.trans hdb⟩)
      (restrictPath hac hcd hdb u) = restrictPath hac hcd hdb u := by
  apply energyPath_injective (intervalMeasure c d)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  ext φ
  have hnew := hartreeDuhamelMap_forward_formula hDensity hSob h0 hfree hret hH
    hcd (energyPath _ u ⟨c, hac, hcd.trans hdb⟩) (restrictPath hac hcd hdb u) t φ
  have hold := hartree_fixedPoint_restart_literal hDensity hSob h0 hfree hret hH
    (hac.trans (hcd.trans hdb)) u0 u hfix ⟨c, hac, hcd.trans hdb⟩
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
      (energyDistribution (energyPath _ u ⟨c, hac, hcd.trans hdb⟩)) φ + Complex.I*z)
    hint).trans (hold.symm.trans
      (congrArg (fun v : EnergyState => energyDistribution v φ)
        (restrictPath_energy hac hcd hdb u t).symm)))

end HartreeF.CriticalPathRestriction
