import FCompatibleIntervalSourceDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace Retarded

/-- Addition of finite interval sources carries the actual weak derivatives. -/
def CompatibleIntervalSource.add {a b : ℝ} (F G : CompatibleIntervalSource a b) :
    CompatibleIntervalSource a b where
  value := F.value + G.value
  gradient := F.gradient + G.gradient
  derivative := by
    have hgrad := ae_all_iff.mpr (fun j => Lp.coeFn_add (F.gradient j) (G.gradient j))
    filter_upwards [F.derivative, G.derivative, Lp.coeFn_add F.value G.value, hgrad]
      with t hF hG hv hg
    intro j
    simp only [Pi.add_apply] at hv hg ⊢
    rw [hv, hg]
    change (lineDerivOpCLM ℂ FreeFlow.TD (coordinate j))
      ((Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ)))
        (F.value t + G.value t)) =
      (Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ)))
        (F.gradient j t + G.gradient j t)
    rw [map_add, map_add, map_add]
    exact congrArg₂ (fun x y : FreeFlow.TD => x + y) (hF j) (hG j)

/-- Complex scaling preserves the actual coordinate derivative relation. -/
def CompatibleIntervalSource.smul {a b : ℝ} (z : ℂ) (F : CompatibleIntervalSource a b) :
    CompatibleIntervalSource a b where
  value := z • F.value
  gradient := z • F.gradient
  derivative := by
    have hgrad := ae_all_iff.mpr (fun j => Lp.coeFn_smul z (F.gradient j))
    filter_upwards [F.derivative, Lp.coeFn_smul z F.value, hgrad] with t hF hv hg
    intro j
    simp only [Pi.smul_apply] at hv hg ⊢
    rw [hv, hg]
    change (lineDerivOpCLM ℂ FreeFlow.TD (coordinate j))
      ((Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ)))
        (z • F.value t)) =
      (Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ)))
        (z • F.gradient j t)
    rw [map_smul, map_smul, map_smul]
    exact congrArg (fun x : FreeFlow.TD => z • x) (hF j)

/-- Zero extension is additive on the native Bochner source classes. -/
theorem extendEndpointSource_add (I : Set ℝ) (hI : MeasurableSet I)
    (F G : LocalEndpointSource I) :
    extendEndpointSource I hI (F + G) =
      extendEndpointSource I hI F + extendEndpointSource I hI G := by
  apply Lp.ext
  filter_upwards [extendEndpointSource_coeFn I hI (F+G),
    extendEndpointSource_coeFn I hI F, extendEndpointSource_coeFn I hI G,
    Lp.coeFn_add (extendEndpointSource I hI F) (extendEndpointSource I hI G),
    (ae_restrict_iff' hI).mp (Lp.coeFn_add F G)] with s hFG hF hG hadd hs
  rw [hFG, hadd, Pi.add_apply, hF, hG]
  by_cases hm : s ∈ I
  · simpa only [Set.indicator_of_mem hm, Pi.add_apply] using hs hm
  · simp only [Set.indicator_of_notMem hm, add_zero]

/-- Zero extension respects complex scalars. -/
theorem extendEndpointSource_smul (I : Set ℝ) (hI : MeasurableSet I)
    (z : ℂ) (F : LocalEndpointSource I) :
    extendEndpointSource I hI (z • F) = z • extendEndpointSource I hI F := by
  apply Lp.ext
  filter_upwards [extendEndpointSource_coeFn I hI (z • F),
    extendEndpointSource_coeFn I hI F,
    Lp.coeFn_smul z (extendEndpointSource I hI F),
    (ae_restrict_iff' hI).mp (Lp.coeFn_smul z F)] with s hzF hF hsmul hs
  rw [hzF, hsmul, Pi.smul_apply, hF]
  by_cases hm : s ∈ I
  · simpa only [Set.indicator_of_mem hm, Pi.smul_apply] using hs hm
  · simp only [Set.indicator_of_notMem hm, smul_zero]

end HartreeF.ActualDuhamelPath
