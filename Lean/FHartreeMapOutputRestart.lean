import FHartreeRestartFormula

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.ActualDuhamelPath
open FreeFlow EnergySpace SobolevStretch StationarySelfTest Retarded
open CriticalPathSpace IntervalTimeTransport ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource

/-- The actual map output restarts at its own state at r, retaining the genuine
Hartree forcing of its original input u. No fixed-point premise is used. -/
theorem hartreeDuhamelMap_output_restart (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (r t : Set.Icc a b) (hrt : (r : ℝ) ≤ (t : ℝ)) :
    energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) t =
      freeEnergyState hDensity hSob ((t : ℝ)-r)
        (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) r) +
      Complex.I • forwardEnergyState hDensity hSob h0 r
        (sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0))
        (sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0))
        (sourceGlobalDerivative (criticalPathIntervalSource hDensity hSob hH hab u 0)) t := by
  have ht := hartreeDuhamelMap_energy_forward hDensity hSob h0 hfree hret hH hab u0 u t
  have hr := hartreeDuhamelMap_energy_forward hDensity hSob h0 hfree hret hH hab u0 u r
  exact ht.trans ((inhomogeneousEnergy_restart hDensity hSob h0 _ _ _
    r.property.1 hrt u0).trans (congrArg
      (fun v : EnergyState => freeEnergyState hDensity hSob ((t : ℝ)-r) v +
        Complex.I • forwardEnergyState hDensity hSob h0 r
          (sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0))
          (sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0))
          (sourceGlobalDerivative (criticalPathIntervalSource hDensity hSob hH hab u 0)) t)
      hr.symm))

/-- The same arbitrary-output restart identity has the literal Hartree source
of u and the focusing Schrodinger coefficient +i. -/
theorem hartreeDuhamelMap_output_restart_literal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (r t : Set.Icc a b) (hrt : (r : ℝ) ≤ (t : ℝ)) (φ : FreeFlow.Test) :
    energyDistribution
      (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) t) φ =
      FreeFlow.free ((t : ℝ)-r)
        (energyDistribution
          (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) r)) φ +
      Complex.I * ∫ s in Set.Ioc (r : ℝ) (t : ℝ), ∫ x,
        (freeTest ((t : ℝ)-s) φ) x •
          forcing alpha kernel (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
  have he := congrArg (fun v : EnergyState => energyDistribution v φ)
    (hartreeDuhamelMap_output_restart hDensity hSob h0 hfree hret hH hab u0 u r t hrt)
  simpa only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
    freeEnergyState_distribution, hartree_forwardEnergyState_restart_scalar] using he

end HartreeF.ActualDuhamelPath
