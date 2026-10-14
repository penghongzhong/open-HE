import FIntervalAdvancedPath

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport Retarded
open SobolevStretch StationarySelfTest ActualStrichartz
local instance advancedLinearityEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance advancedLinearityGraphNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule
  intervalAdvancedCriticalPath energyPath criticalGradient energyDistribution
  restrictedL2CLM Lp.toTemperedDistributionCLM extendEndpointSource

/-- Exact add identity for the actual future graph path. -/
theorem intervalAdvancedCriticalPath_add (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F G : CompatibleIntervalSource a b) :
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret (F.add G) =
      intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F +
      intervalAdvancedCriticalPath hDensity hSob h0 hfree hret G := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  let P : CompatibleIntervalSource a b → CriticalPath (intervalMeasure a b) :=
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
  let L := energyPath (intervalMeasure a b)
  let R := restrictedL2CLM h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t
  let D := Lp.toTemperedDistributionCLM ℂ (volume : Measure FreeFlow.V) 2
  let eF := sourceGlobalValue F
  let eG := sourceGlobalValue G
  have hA := intervalAdvancedCriticalPath_distribution hDensity hSob h0 hfree hret (F.add G) t
  have hF := intervalAdvancedCriticalPath_distribution hDensity hSob h0 hfree hret F t
  have hG := intervalAdvancedCriticalPath_distribution hDensity hSob h0 hfree hret G t
  have hp : L (P F + P G) t = L (P F) t + L (P G) t :=
    congrArg (fun f : C(Set.Icc a b, EnergyState) => f t) (L.map_add (P F) (P G))
  have hd := energyDistribution.map_add (L (P F) t) (L (P G) t)
  have he : sourceGlobalValue (F.add G) = eF + eG :=
    extendEndpointSource_add (Set.Icc a b) measurableSet_Icc F.value G.value
  have ho : D (R (sourceGlobalValue (F.add G))) = D (R eF) + D (R eG) :=
    (congrArg (fun H => D (R H)) he).trans
      ((congrArg D (R.map_add eF eG)).trans (D.map_add (R eF) (R eG)))
  exact hA.trans (ho.trans ((congrArg₂ (fun x y : FreeFlow.TD => x + y) hF.symm hG.symm).trans
    (hd.symm.trans (congrArg energyDistribution hp.symm))))

/-- Exact smul identity for the actual future graph path. -/
theorem intervalAdvancedCriticalPath_smul (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (z : ℂ) (F : CompatibleIntervalSource a b) :
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret (CompatibleIntervalSource.smul z F) =
      z • intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  let P : CompatibleIntervalSource a b → CriticalPath (intervalMeasure a b) :=
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
  let L := energyPath (intervalMeasure a b)
  let R := restrictedL2CLM h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t
  let D := Lp.toTemperedDistributionCLM ℂ (volume : Measure FreeFlow.V) 2
  let eF := sourceGlobalValue F
  have hA := intervalAdvancedCriticalPath_distribution hDensity hSob h0 hfree hret (CompatibleIntervalSource.smul z F) t
  have hF := intervalAdvancedCriticalPath_distribution hDensity hSob h0 hfree hret F t
  have hp : L (z • P F) t = z • L (P F) t :=
    congrArg (fun f : C(Set.Icc a b, EnergyState) => f t) (L.map_smul z (P F))
  have hd := energyDistribution.map_smul z (L (P F) t)
  have he : sourceGlobalValue (CompatibleIntervalSource.smul z F) = z • eF :=
    extendEndpointSource_smul (Set.Icc a b) measurableSet_Icc z F.value
  have ho : D (R (sourceGlobalValue (CompatibleIntervalSource.smul z F))) = z • D (R eF) :=
    (congrArg (fun H => D (R H)) he).trans
      ((congrArg D (R.map_smul z eF)).trans (D.map_smul z (R eF)))
  exact hA.trans (ho.trans ((congrArg (fun x : FreeFlow.TD => z • x) hF.symm).trans
    (hd.symm.trans (congrArg energyDistribution hp.symm))))

/-- Exact sub identity for the actual future graph path. -/
theorem intervalAdvancedCriticalPath_sub (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F G : CompatibleIntervalSource a b) :
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret (F.sub G) =
      intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F -
      intervalAdvancedCriticalPath hDensity hSob h0 hfree hret G := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  let P : CompatibleIntervalSource a b → CriticalPath (intervalMeasure a b) :=
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
  let L := energyPath (intervalMeasure a b)
  let R := restrictedL2CLM h0 (Set.Ioc (t : ℝ) b) measurableSet_Ioc t
  let D := Lp.toTemperedDistributionCLM ℂ (volume : Measure FreeFlow.V) 2
  let eF := sourceGlobalValue F
  let eG := sourceGlobalValue G
  have hA := intervalAdvancedCriticalPath_distribution hDensity hSob h0 hfree hret (F.sub G) t
  have hF := intervalAdvancedCriticalPath_distribution hDensity hSob h0 hfree hret F t
  have hG := intervalAdvancedCriticalPath_distribution hDensity hSob h0 hfree hret G t
  have hp : L (P F - P G) t = L (P F) t - L (P G) t :=
    congrArg (fun f : C(Set.Icc a b, EnergyState) => f t) (L.map_sub (P F) (P G))
  have hd := energyDistribution.map_sub (L (P F) t) (L (P G) t)
  have he : sourceGlobalValue (F.sub G) = eF - eG :=
    extendEndpointSource_sub (Set.Icc a b) measurableSet_Icc F.value G.value
  have ho : D (R (sourceGlobalValue (F.sub G))) = D (R eF) - D (R eG) :=
    (congrArg (fun H => D (R H)) he).trans
      ((congrArg D (R.map_sub eF eG)).trans (D.map_sub (R eF) (R eG)))
  exact hA.trans (ho.trans ((congrArg₂ (fun x y : FreeFlow.TD => x - y) hF.symm hG.symm).trans
    (hd.symm.trans (congrArg energyDistribution hp.symm))))

/-- The derived E+W source-difference estimate is interval independent. -/
theorem intervalAdvancedCriticalPath_sub_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F G : CompatibleIntervalSource a b) :
    ‖intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F -
      intervalAdvancedCriticalPath hDensity hSob h0 hfree hret G‖ ≤
      max (energyEndpointConstant K C0) (Ch * C0 + Cr) * ‖F.gradient - G.gradient‖ := by
  rw [← intervalAdvancedCriticalPath_sub]
  exact intervalAdvancedCriticalPath_norm hDensity hSob h0 hfree hret (F.sub G)

/-- The individual sharp-W coordinate differences retain the derived constant. -/
theorem intervalAdvancedCriticalPath_sub_gradient_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (F G : CompatibleIntervalSource a b) (j : Fin 3) :
    ‖criticalGradient _ j (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F -
      intervalAdvancedCriticalPath hDensity hSob h0 hfree hret G)‖ ≤
      (Ch * C0 + Cr) * ‖F.gradient j - G.gradient j‖ := by
  rw [← intervalAdvancedCriticalPath_sub]
  exact intervalAdvancedCriticalPath_gradient_norm hDensity hSob h0 hfree hret (F.sub G) j

end HartreeF.ActualDuhamelPath
