import FIntervalRetardedRestart

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

/-- The exact scalar forward formula for the same zero-extended interval source. -/
theorem sourceGlobal_forward_scalar (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (r t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (forwardEnergyState hDensity hSob h0 r
      (sourceGlobalValue F) (sourceGlobalGradient F) (sourceGlobalDerivative F) t) φ =
      ∫ s in Set.Ioc (r : ℝ) (t : ℝ),
        Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) := by
  rw [forwardEnergyState, restrictedEnergyState, l2EnergyState_distribution,
    sourceGlobalValue, restrictedL2_extend_scalar]
  have hsub : Set.Ioc (r : ℝ) (t : ℝ) ⊆ Set.Icc a b :=
    fun _ hs => ⟨r.property.1.trans hs.1.le, hs.2.trans t.property.2⟩
  rw [Set.inter_eq_right.mpr hsub]

/-- The restarted source is still the original actual Hartree forcing on the
smaller forward interval; no new source representative is assumed. -/
theorem hartree_forwardEnergyState_restart_scalar (hDensity : OrdinaryH1Density)
    {K C0 alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b))
    (r t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (forwardEnergyState hDensity hSob h0 r
      (sourceGlobalValue (criticalPathIntervalSource hDensity hSob hH hab u 0))
      (sourceGlobalGradient (criticalPathIntervalSource hDensity hSob hH hab u 0))
      (sourceGlobalDerivative (criticalPathIntervalSource hDensity hSob hH hab u 0)) t) φ =
      ∫ s in Set.Ioc (r : ℝ) (t : ℝ), ∫ x,
        (freeTest ((t : ℝ)-s) φ) x •
          forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
  refine (sourceGlobal_forward_scalar hDensity hSob h0
    (criticalPathIntervalSource hDensity hSob hH hab u 0) r t φ).trans ?_
  have hsub : Set.Ioc (r : ℝ) (t : ℝ) ⊆ Set.Icc a b :=
    fun _ hs => ⟨r.property.1.trans hs.1.le, hs.2.trans t.property.2⟩
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
    (criticalPathIntervalSource_single_coeFn hDensity hSob hH hab u)] with s hs
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  exact hs.mono (fun x hx => congrArg (fun z : ℂ => (freeTest ((t : ℝ)-s) φ) x • z) hx)

/-- Every actual fixed point satisfies the literal Hartree equation restarted
at any internal time r, with the same solution and the same +i coefficient. -/
theorem hartree_fixedPoint_restart_literal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u)
    (r t : Set.Icc a b) (hrt : (r : ℝ) ≤ (t : ℝ)) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ u t) φ =
      FreeFlow.free ((t : ℝ)-r) (energyDistribution (energyPath _ u r)) φ +
        Complex.I * ∫ s in Set.Ioc (r : ℝ) (t : ℝ), ∫ x,
          (freeTest ((t : ℝ)-s) φ) x •
            forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) s)) x := by
  have he := congrArg (fun v : EnergyState => energyDistribution v φ)
    (hartree_fixedPoint_restart hDensity hSob h0 hfree hret hH hab u0 u hfix r t hrt)
  simpa only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
    freeEnergyState_distribution, hartree_forwardEnergyState_restart_scalar] using he

end HartreeF.ActualDuhamelPath
