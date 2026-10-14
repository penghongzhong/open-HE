import FActualHartreeDuhamelMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
namespace HartreeF.CriticalUniqueness
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource

/-- The literal finite-forward mild equation for the existing canonical path.
This definition includes the actual convolution forcing and every Schwartz test. -/
def IsMildHartreePath {a b : ℝ} (hab : a ≤ b) (alpha kernel : ℝ)
    (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b)) : Prop :=
  ∀ t : Set.Icc a b, ∀ φ : FreeFlow.Test,
    energyDistribution (energyPath _ u t) φ =
      FreeFlow.free ((t : ℝ)-a) (energyDistribution u0) φ + Complex.I *
        ∫ s in Set.Ioc a (t : ℝ), ∫ x,
          (freeTest ((t : ℝ)-s) φ) x •
            forcing alpha kernel (energyValue (extendEnergyPath hab (energyPath _ u) s)) x

/-- The literal mild equation and the actual Phi fixed-point equation are
equivalent on the canonical graph; no source or output witness is assumed. -/
theorem isMildHartreePath_iff_fixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b)) :
    IsMildHartreePath hab alpha kernel u0 u ↔
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u := by
  constructor
  · intro h
    apply energyPath_injective (intervalMeasure a b)
    apply ContinuousMap.ext
    intro t
    apply energyDistribution_injective
    ext φ
    exact (hartreeDuhamelMap_forward_formula hDensity hSob h0 hfree hret hH hab u0 u t φ).trans
      (h t φ).symm
  · intro h t φ
    exact (congrArg (fun v : CriticalPath (intervalMeasure a b) =>
      energyDistribution (energyPath _ v t) φ) h).symm.trans
        (hartreeDuhamelMap_forward_formula hDensity hSob h0 hfree hret hH hab u0 u t φ)

end HartreeF.CriticalUniqueness
