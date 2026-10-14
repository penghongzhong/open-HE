import FActualHartreeDuhamelMap
import FLocalRetardedEnergySup

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

/-- The scalar source fixes all of its compatible Bochner derivative classes. -/
theorem CompatibleIntervalSource.ext_value {a b : ℝ} (F G : CompatibleIntervalSource a b)
    (h : F.value = G.value) : F = G := by
  have hg : F.gradient = G.gradient := by
    funext j
    apply Lp.ext
    filter_upwards [F.derivative, G.derivative] with t hF hG
    exact Lp.ext (spatial_ae_eq_of_distribution_eq _ _
      ((hF j).symm.trans (by simpa only [h] using hG j)))
  cases F
  cases G
  cases h
  cases hg
  rfl

/-- Actual source subtraction, including the native a.e. derivative relation. -/
def CompatibleIntervalSource.sub {a b : ℝ} (F G : CompatibleIntervalSource a b) :
    CompatibleIntervalSource a b where
  value := F.value - G.value
  gradient := F.gradient - G.gradient
  derivative := by
    have hgrad := ae_all_iff.mpr (fun j => Lp.coeFn_sub (F.gradient j) (G.gradient j))
    filter_upwards [F.derivative, G.derivative, Lp.coeFn_sub F.value G.value, hgrad]
      with t hF hG hv hg
    intro j
    simp only [Pi.sub_apply] at hv hg ⊢
    rw [hv, hg]
    change (lineDerivOpCLM ℂ FreeFlow.TD (coordinate j))
      ((Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ)))
        (F.value t - G.value t)) =
      (Lp.toTemperedDistributionCLM ℂ volume (ENNReal.ofReal (6/5 : ℝ)))
        (F.gradient j t - G.gradient j t)
    rw [map_sub, map_sub, map_sub]
    exact congrArg₂ (fun x y : FreeFlow.TD => x - y) (hF j) (hG j)

/-- Nonlinear source subtraction is a theorem about the produced input classes. -/
theorem criticalPathIntervalSource_sub_zero (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u v : CriticalPath (intervalMeasure a b)) :
    (criticalPathIntervalSource hDensity hSob hH hab u 0).sub
      (criticalPathIntervalSource hDensity hSob hH hab v 0) =
        criticalPathIntervalSource hDensity hSob hH hab u v := by
  apply CompatibleIntervalSource.ext_value
  simp only [CompatibleIntervalSource.sub, criticalPathIntervalSource_value]
  abel

end HartreeF.ActualDuhamelPath
