import FForwardRetardedRestart
import FActualHartreeDuhamelMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.ActualDuhamelPath
open FreeFlow EnergySpace SobolevStretch StationarySelfTest Retarded
open CriticalPathSpace IntervalTimeTransport ActualStrichartz ForcingDomain

/-- The zero extension of the actual finite-interval scalar source. -/
def sourceGlobalValue {a b : ℝ} (F : CompatibleIntervalSource a b) : EndpointSource :=
  extendEndpointSource (Set.Icc a b) measurableSet_Icc F.value

/-- The same extension for the three genuine weak derivative coordinates. -/
def sourceGlobalGradient {a b : ℝ} (F : CompatibleIntervalSource a b)
    (j : Fin 3) : EndpointSource :=
  extendEndpointSource (Set.Icc a b) measurableSet_Icc (F.gradient j)

theorem sourceGlobalDerivative {a b : ℝ} (F : CompatibleIntervalSource a b)
    (j : Fin 3) : ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (sourceGlobalValue F s)) =
        Lp.toTemperedDistribution (sourceGlobalGradient F j s) :=
  ae_all_iff.mp (extendEndpointSource_coordinate_derivatives (Set.Icc a b)
    measurableSet_Icc F.value F.gradient F.derivative) j

/-- Actual local-source retarded output equals its forward energy realization. -/
theorem intervalRetardedCriticalPath_eq_forward (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b)
    (t : Set.Icc a b) :
    energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) t =
      forwardEnergyState hDensity hSob h0 a (sourceGlobalValue F)
        (sourceGlobalGradient F) (sourceGlobalDerivative F) t := by
  apply energyDistribution_injective
  ext φ
  rw [intervalRetardedCriticalPath_forward_scalar]
  rw [forwardEnergyState, restrictedEnergyState, l2EnergyState_distribution]
  rw [sourceGlobalValue, restrictedL2_extend_scalar]
  have hset : Set.Icc a b ∩ Set.Ioc a (t : ℝ) = Set.Ioc a (t : ℝ) :=
    Set.inter_eq_right.mpr (fun _ hs => ⟨hs.1.le, hs.2.trans t.property.2⟩)
  rw [hset]

/-- An interval's actual retarded energy path restarts at every internal time. -/
theorem intervalRetardedCriticalPath_restart (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b)
    (r t : Set.Icc a b) (hrt : (r : ℝ) ≤ (t : ℝ)) :
    energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) t =
      freeEnergyState hDensity hSob ((t : ℝ)-r)
        (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) r) +
      forwardEnergyState hDensity hSob h0 r (sourceGlobalValue F)
        (sourceGlobalGradient F) (sourceGlobalDerivative F) t := by
  rw [intervalRetardedCriticalPath_eq_forward, intervalRetardedCriticalPath_eq_forward]
  exact forwardEnergyState_restart hDensity hSob h0 _ _ _ r.property.1 hrt

attribute [local irreducible] hartreeDuhamelMap criticalPathIntervalSource
  energySubmodule criticalPathSubmodule energyPath energyDistribution

/-- The actual Hartree map is the same free-plus-forward energy trajectory. -/
theorem hartreeDuhamelMap_energy_forward (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (t : Set.Icc a b) :
    energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) t =
      freeEnergyState hDensity hSob ((t : ℝ)-a) u0 + Complex.I •
        forwardEnergyState hDensity hSob h0 a
          (sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0))
          (sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0))
          (sourceGlobalDerivative (criticalPathIntervalSource hDensity hSob hH hab u 0)) t := by
  simp only [hartreeDuhamelMap, map_add, map_smul, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, freeCriticalPath_energy,
    intervalRetardedCriticalPath_eq_forward]
  rw [← freeEnergyState_add_time]
  rfl

/-- A literal fixed point restarts with its own actual state and its own source.
This is an exact identity; it does not assume a solution at the new initial time. -/
theorem hartree_fixedPoint_restart (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u)
    (r t : Set.Icc a b) (hrt : (r : ℝ) ≤ (t : ℝ)) :
    energyPath _ u t = freeEnergyState hDensity hSob ((t : ℝ)-r) (energyPath _ u r) +
      Complex.I • forwardEnergyState hDensity hSob h0 r
        (sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0))
        (sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0))
        (sourceGlobalDerivative (criticalPathIntervalSource hDensity hSob hH hab u 0)) t := by
  have ht := hartreeDuhamelMap_energy_forward hDensity hSob h0 hfree hret hH hab u0 u t
  have hr := hartreeDuhamelMap_energy_forward hDensity hSob h0 hfree hret hH hab u0 u r
  have hte := (congrArg (fun v : CriticalPath (intervalMeasure a b) =>
    energyPath _ v t) hfix).symm.trans ht
  have hre := (congrArg (fun v : CriticalPath (intervalMeasure a b) =>
    energyPath _ v r) hfix).symm.trans hr
  exact hte.trans ((inhomogeneousEnergy_restart hDensity hSob h0 _ _ _
    r.property.1 hrt u0).trans (congrArg
      (fun v : EnergyState => freeEnergyState hDensity hSob ((t : ℝ)-r) v +
        Complex.I • forwardEnergyState hDensity hSob h0 r
          (sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0))
          (sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0))
          (sourceGlobalDerivative (criticalPathIntervalSource hDensity hSob hH hab u 0)) t)
      hre.symm))

end HartreeF.ActualDuhamelPath
