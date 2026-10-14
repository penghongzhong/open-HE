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

/-- The energy datum at time zero produced by the entire finite source interval.
The value and all three genuine derivative sources are extended by zero. -/
def intervalTotalSourceEnergy (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) : EnergyState :=
  restrictedEnergyState hDensity hSob h0 (sourceGlobalValue F)
    (sourceGlobalGradient F) (sourceGlobalDerivative F)
    (Set.Ioc a b) measurableSet_Ioc 0

/-- Free propagation transports the total source datum to the same full
interval integral at the requested evaluation time. -/
theorem intervalTotalSourceEnergy_free_eq_restricted (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (t : ℝ) :
    freeEnergyState hDensity hSob t (intervalTotalSourceEnergy hDensity hSob h0 F) =
      restrictedEnergyState hDensity hSob h0 (sourceGlobalValue F)
        (sourceGlobalGradient F) (sourceGlobalDerivative F)
        (Set.Ioc a b) measurableSet_Ioc t := by
  apply energyDistribution_injective
  ext φ
  rw [freeEnergyState_distribution, free_apply, intervalTotalSourceEnergy,
    restrictedEnergyState_scalar, restrictedEnergyState_scalar]
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by
    simpa only [add_zero] using scalarIntegrand_transport t 0 s (sourceGlobalValue F) φ)

theorem intervalTotalSourceEnergy_free_scalar (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (t : ℝ) (φ : FreeFlow.Test) :
    energyDistribution
        (freeEnergyState hDensity hSob t (intervalTotalSourceEnergy hDensity hSob h0 F)) φ =
      ∫ s in Set.Ioc a b, scalarIntegrand t (sourceGlobalValue F) φ s := by
  rw [intervalTotalSourceEnergy_free_eq_restricted, restrictedEnergyState_scalar]

/-- The future contribution is obtained by subtracting the actual past
contribution from the freely propagated total source state. -/
def intervalFutureEnergyState (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (t : ℝ) : EnergyState :=
  freeEnergyState hDensity hSob t (intervalTotalSourceEnergy hDensity hSob h0 F) -
    forwardEnergyState hDensity hSob h0 a (sourceGlobalValue F)
      (sourceGlobalGradient F) (sourceGlobalDerivative F) t

/-- The split uses the genuine integrability retained in OrdinaryEndpointBound.
The upper integration endpoint and evaluation time are allowed to differ. -/
theorem scalarIntegrand_interval_split {C0 a t b : ℝ}
    (h0 : OrdinaryEndpointBound C0) (hat : a ≤ t) (htb : t ≤ b)
    (F : EndpointSource) (φ : FreeFlow.Test) :
    (∫ s in Set.Ioc a b, scalarIntegrand t F φ s) =
      (∫ s in Set.Ioc a t, scalarIntegrand t F φ s) +
        ∫ s in Set.Ioc t b, scalarIntegrand t F φ s := by
  rw [← Set.Ioc_union_Ioc_eq_Ioc hat htb]
  exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (h0.2 _ measurableSet_Ioc t F φ).1 (h0.2 _ measurableSet_Ioc t F φ).1

/-- Exact energy-space identity with the integral over (t,b]. -/
theorem intervalFutureEnergyState_eq_restricted (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) :
    intervalFutureEnergyState hDensity hSob h0 F t =
      restrictedEnergyState hDensity hSob h0 (sourceGlobalValue F)
        (sourceGlobalGradient F) (sourceGlobalDerivative F)
        (Set.Ioc (t : ℝ) b) measurableSet_Ioc t := by
  apply energyDistribution_injective
  ext φ
  rw [intervalFutureEnergyState, map_sub, sub_apply,
    intervalTotalSourceEnergy_free_scalar, forwardEnergyState_scalar,
    restrictedEnergyState_scalar]
  rw [scalarIntegrand_interval_split h0 t.property.1 t.property.2]
  abel

theorem intervalFutureEnergyState_global_scalar (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (intervalFutureEnergyState hDensity hSob h0 F t) φ =
      ∫ s in Set.Ioc (t : ℝ) b, scalarIntegrand t (sourceGlobalValue F) φ s := by
  rw [intervalFutureEnergyState_eq_restricted, restrictedEnergyState_scalar]

/-- The future state is the literal finite-interval source integral in local
source coordinates, without an additional phase or forcing-sign factor. -/
theorem intervalFutureEnergyState_scalar (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (intervalFutureEnergyState hDensity hSob h0 F t) φ =
      ∫ s in Set.Ioc (t : ℝ) b,
        Lp.toTemperedDistribution (F.value s) (freeTest ((t : ℝ)-s) φ) := by
  rw [intervalFutureEnergyState_eq_restricted, restrictedEnergyState,
    l2EnergyState_distribution, sourceGlobalValue, restrictedL2_extend_scalar]
  have hset : Set.Icc a b ∩ Set.Ioc (t : ℝ) b = Set.Ioc (t : ℝ) b :=
    Set.inter_eq_right.mpr (fun _ hs => ⟨t.property.1.trans hs.1.le, hs.2⟩)
  rw [hset]

/-- Distribution identity through the already constructed bounded L2 operator. -/
theorem intervalFutureEnergyState_distribution (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) :
    energyDistribution (intervalFutureEnergyState hDensity hSob h0 F t) =
      Lp.toTemperedDistributionCLM ℂ (volume : Measure FreeFlow.V) 2
        (restrictedL2CLM h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t
          (sourceGlobalValue F)) := by
  rw [intervalFutureEnergyState_eq_restricted, restrictedEnergyState,
    l2EnergyState_distribution]
  rfl

/-- The gradient coordinates are the true weak derivatives produced from the
same compatible source, rather than independent projected witnesses. -/
theorem intervalFutureEnergyState_gradient (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) (t : Set.Icc a b) (j : Fin 3) :
    energyGradient j (intervalFutureEnergyState hDensity hSob h0 F t) =
      restrictedL2 h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t
        (sourceGlobalGradient F j) := by
  rw [intervalFutureEnergyState_eq_restricted, restrictedEnergyState_gradient]

/-- The advanced energy trajectory vanishes exactly at the terminal time. -/
theorem intervalFutureEnergyState_right_zero (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hab : a ≤ b) (F : CompatibleIntervalSource a b) :
    intervalFutureEnergyState hDensity hSob h0 F b = 0 := by
  apply energyDistribution_injective
  ext φ
  have hscalar := intervalFutureEnergyState_scalar hDensity hSob h0 F
    (⟨b, hab, le_rfl⟩ : Set.Icc a b) φ
  simpa using hscalar

/-- Energy continuity follows from the full free state and existing forward
energy continuity, with no advanced Strichartz hypothesis. -/
theorem intervalFutureEnergyState_time_continuous (hDensity : OrdinaryH1Density)
    {K C0 a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (F : CompatibleIntervalSource a b) :
    Continuous (intervalFutureEnergyState hDensity hSob h0 F) := by
  exact (freeEnergyState_time_continuous hDensity hSob
    (intervalTotalSourceEnergy hDensity hSob h0 F)).sub
      (forwardEnergyState_time_continuous hDensity hSob h0 (sourceGlobalValue F)
        (sourceGlobalGradient F) (sourceGlobalDerivative F) a)

end HartreeF.ActualDuhamelPath
