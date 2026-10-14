import FCompatibleIntervalSourceDifference
import FActualDuhamelCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace LocalScalarSource ForcingDomain
open SobolevStretch StationarySelfTest Retarded ActualStrichartz
attribute [local irreducible] criticalPathIntervalSource intervalRetardedCriticalPath
  freeCriticalPath criticalPathOfGlobalFields CriticalJointSources.jointFields
  energyPath energyDistribution criticalGradient
  energySubmodule criticalPathSubmodule

/-- Evaluation of the abstract path projection preserves subtraction. -/
theorem criticalPath_energy_sub_apply {a b : ℝ}
    (u v : CriticalPath (intervalMeasure a b)) (t : Set.Icc a b) :
    energyPath _ (u - v) t = energyPath _ u t - energyPath _ v t := by
  exact congrArg (fun f : C(Set.Icc a b, EnergyState) => f t)
    ((energyPath (intervalMeasure a b)).map_sub u v)

/-- The constructed energy distribution is the image of the actual linear
retarded L2 operator. No output linearity hypothesis is used. -/
theorem intervalRetardedCriticalPath_distribution (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b)
    (t : Set.Icc a b) :
    energyDistribution (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) t) =
      (Lp.toTemperedDistributionCLM ℂ volume 2)
        ((restrictedL2CLM h0 (Set.Iio (t : ℝ)) measurableSet_Iio t)
          (extendEndpointSource (Set.Icc a b) measurableSet_Icc F.value)) := by
  unfold intervalRetardedCriticalPath
  rw [retardedCriticalPath_energy, retardedEnergyState, restrictedEnergyState,
    l2EnergyState_distribution]
  rfl

attribute [local irreducible] restrictedL2CLM Lp.toTemperedDistributionCLM
  extendEndpointSource

/-- Subtraction through the actual three linear source maps, with all source
arguments kept abstract during the native CLM applications. -/
theorem localRetardedDistribution_sub {C0 a b : ℝ} (h0 : OrdinaryEndpointBound C0)
    (F G : LocalEndpointSource (Set.Icc a b)) (t : ℝ) :
    (Lp.toTemperedDistributionCLM ℂ volume 2)
      ((restrictedL2CLM h0 (Set.Iio t) measurableSet_Iio t)
        (extendEndpointSource (Set.Icc a b) measurableSet_Icc (F-G))) =
      (Lp.toTemperedDistributionCLM ℂ volume 2)
        ((restrictedL2CLM h0 (Set.Iio t) measurableSet_Iio t)
          (extendEndpointSource (Set.Icc a b) measurableSet_Icc F)) -
      (Lp.toTemperedDistributionCLM ℂ volume 2)
        ((restrictedL2CLM h0 (Set.Iio t) measurableSet_Iio t)
          (extendEndpointSource (Set.Icc a b) measurableSet_Icc G)) := by
  let R : EndpointSource →L[ℂ] FreeFlow.L2 :=
    restrictedL2CLM h0 (Set.Iio t) measurableSet_Iio t
  let D : FreeFlow.L2 →L[ℂ] FreeFlow.TD := Lp.toTemperedDistributionCLM ℂ volume 2
  let eF := extendEndpointSource (Set.Icc a b) measurableSet_Icc F
  let eG := extendEndpointSource (Set.Icc a b) measurableSet_Icc G
  exact (congrArg (fun H => D (R H))
    (extendEndpointSource_sub (Set.Icc a b) measurableSet_Icc F G)).trans
      ((congrArg D (R.map_sub eF eG)).trans (D.map_sub (R eF) (R eG)))

set_option diagnostics true in
/-- Linearity holds in the entire path graph, since the energy trajectory
uniquely fixes its three Bochner coordinates. -/
theorem intervalRetardedCriticalPath_sub (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F G : CompatibleIntervalSource a b) :
    intervalRetardedCriticalPath hDensity hSob h0 h (F.sub G) =
      intervalRetardedCriticalPath hDensity hSob h0 h F -
        intervalRetardedCriticalPath hDensity hSob h0 h G := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  have hA := intervalRetardedCriticalPath_distribution hDensity hSob h0 h (F.sub G) t
  have hF := intervalRetardedCriticalPath_distribution hDensity hSob h0 h F t
  have hG := intervalRetardedCriticalPath_distribution hDensity hSob h0 h G t
  have hP := criticalPath_energy_sub_apply
    (intervalRetardedCriticalPath hDensity hSob h0 h F)
    (intervalRetardedCriticalPath hDensity hSob h0 h G) t
  have hD := energyDistribution.map_sub
    (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F) t)
    (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h G) t)
  exact hA.trans ((localRetardedDistribution_sub h0 F.value G.value t).trans
    ((congrArg₂ (fun x y : FreeFlow.TD => x-y) hF.symm hG.symm).trans
      (hD.symm.trans (congrArg energyDistribution hP.symm))))

/-- The continuous-time energy supremum of the actual local retarded path. -/
theorem intervalRetardedCriticalPath_energy_norm (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b) :
    ‖energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F)‖ ≤
      energyEndpointConstant K C0 * ‖F.gradient‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (energyEndpointConstant_nonneg h0) (norm_nonneg F.gradient))).mpr
  intro t
  unfold intervalRetardedCriticalPath
  rw [retardedCriticalPath_energy]
  have hb := retardedEnergyState_norm hDensity hSob h0
    (extendEndpointSource (Set.Icc a b) measurableSet_Icc F.value)
    (fun j => extendEndpointSource (Set.Icc a b) measurableSet_Icc (F.gradient j))
    (ae_all_iff.mp (extendEndpointSource_coordinate_derivatives (Set.Icc a b)
      measurableSet_Icc F.value F.gradient F.derivative)) t
  rwa [extendEndpointSource_family_norm] at hb

/-- All three W coordinates obey the retained numerical retarded estimate. -/
theorem intervalRetardedCriticalPath_gradient_family_norm (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b) :
    ‖fun j => criticalGradient _ j
      (intervalRetardedCriticalPath hDensity hSob h0 h F)‖ ≤ C * ‖F.gradient‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg h.1 (norm_nonneg F.gradient))).mpr
  intro j
  have hb := intervalRetardedCriticalPath_gradient_bound hDensity hSob h0 h F j
  have hr : ‖criticalGradient _ j
      (intervalRetardedCriticalPath hDensity hSob h0 h F)‖ ≤ C * ‖F.gradient j‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg h.1 (norm_nonneg _))).mp
    simpa only [ofReal_norm] using hb
  exact hr.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm F.gradient j) h.1)

/-- Full E+W path bound: the product norm uses the maximum, so no sum or
unjustified replacement of the vector-to-coordinate operator is introduced. -/
theorem intervalRetardedCriticalPath_norm (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b) :
    ‖intervalRetardedCriticalPath hDensity hSob h0 h F‖ ≤
      max (energyEndpointConstant K C0) C * ‖F.gradient‖ := by
  rw [criticalPath_norm]
  apply max_le
  · exact (intervalRetardedCriticalPath_energy_norm hDensity hSob h0 h F).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · exact (intervalRetardedCriticalPath_gradient_family_norm hDensity hSob h0 h F).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem intervalRetardedCriticalPath_sub_norm (hDensity : OrdinaryH1Density)
    {K C0 C a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F G : CompatibleIntervalSource a b) :
    ‖intervalRetardedCriticalPath hDensity hSob h0 h F -
      intervalRetardedCriticalPath hDensity hSob h0 h G‖ ≤
      max (energyEndpointConstant K C0) C * ‖F.gradient - G.gradient‖ := by
  rw [← intervalRetardedCriticalPath_sub]
  exact intervalRetardedCriticalPath_norm hDensity hSob h0 h (F.sub G)

end HartreeF.ActualDuhamelPath
