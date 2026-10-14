import FRegularizedDuhamelDerivative
import FRegularizedMildBochnerConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology ENNReal
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace CriticalUniqueness IntervalTimeTransport ForcingContinuity ForcingDomain
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution

/-- The actual strong regularized equation derived from the literal Hartree
Duhamel formula. There is no PDE-differentiability, original-value L2,
variance, or regularized-equation premise. The point is strictly interior. -/
theorem actual_mild_regularized_hasDerivAt (hDensity : OrdinaryH1Density)
    {K alpha c a b t : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (B : OrdinaryBesselLp sourceExponent) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha c u0 u) (n : ℕ) (ht : t ∈ Set.Ioo a b) :
    HasDerivAt (fun s => J hDensity hSob n (extendEnergyPath hab (energyPath _ u) s))
      (Complex.I • deltaJ hDensity hSob n (extendEnergyPath hab (energyPath _ u) t) +
        Complex.I • S.sourceJ B n (forcingLp hH
          (energyValue (extendEnergyPath hab (energyPath _ u) t)))) t := by
  let f := sourcePath hDensity hSob S B hH hab u n
  let v := extendEnergyPath hab (energyPath _ u)
  have he (s : ℝ) (hs : s ∈ Set.Icc a b) : J hDensity hSob n (v s) =
      energyDuhamel hDensity hSob a (J hDensity hSob n u0) f s := by
    have H := actual_mild_regularized_bochner hDensity hSob S B hH hab u0 u hmild n ⟨s,hs⟩
    have hx : v s = energyPath _ u ⟨s,hs⟩ :=
      extendEnergyPath_val hab (energyPath _ u) ⟨s,hs⟩
    rw [hx]
    exact H
  have h := energyDuhamel_hasDerivAt_of_J hDensity hSob a (J hDensity hSob n u0) f
    f.continuous n (v t) t (he t ⟨ht.1.le,ht.2.le⟩).symm
  change HasDerivAt (fun s => J hDensity hSob n (v s))
    (Complex.I • deltaJ hDensity hSob n (v t) + Complex.I • f t) t
  apply h.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
  exact he s hs

#print energyDuhamel
#check @actual_mild_regularized_hasDerivAt
#print axioms actual_mild_regularized_hasDerivAt
end HartreeF.Regularization.Actual
