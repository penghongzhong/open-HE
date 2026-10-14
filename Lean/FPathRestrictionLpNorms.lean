import FActualSValueRealization
import FCriticalPathRestriction
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Exact restriction identities for the actual scalar S realization and
the same canonical gradient coordinates. No partition is postulated. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ActualPathPartitions
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction
open ActualSTail SobolevStretch StationarySelfTest CriticalSourceBounds CriticalJointSources
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields
  criticalGradient restrictPath

theorem restrictIntervalLp_norm_eq_lpNorm {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) {a b c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (f : Lp E p (intervalMeasure a b)) :
    ‖restrictIntervalLp p hac hcd hdb f‖ =
      lpNorm (toLocalLp (hac.trans (hcd.trans hdb)) p f) p (localMeasure c d) := by
  rw [restrictIntervalLp, toIntervalLp_norm, shrinkLp, Lp.norm_toLp]
  rfl

theorem pathValueLp_restrict (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (q : CriticalPath (intervalMeasure a b)) :
    pathValueLp hDensity hSob (restrictPath hac hcd hdb q) =
      restrictIntervalLp 10 hac hcd hdb (pathValueLp hDensity hSob q) := by
  apply Lp.ext
  filter_upwards [pathValueLp_coeFn hDensity hSob (restrictPath hac hcd hdb q),
    restrictIntervalLp_coeFn 10 hac hcd hdb (pathValueLp hDensity hSob q),
    ae_intervalInclusion hac hcd hdb (pathValueLp_coeFn hDensity hSob q)]
    with t hv hr hq
  rw [hr]
  apply Lp.ext
  rw [restrictPath_energy] at hv
  exact hv.trans hq.symm

theorem restricted_pathValueSize_eq (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (q : CriticalPath (intervalMeasure a b)) :
    pathValueSize (intervalMeasure c d) (restrictPath hac hcd hdb q) =
      eLpNorm (toLocalLp (hac.trans (hcd.trans hdb)) 10 (pathValueLp hDensity hSob q))
        10 (localMeasure c d) := by
  rw [← pathValueLp_enorm hDensity hSob, ← ofReal_norm, pathValueLp_restrict,
    restrictIntervalLp_norm_eq_lpNorm]
  exact ofReal_lpNorm ((Lp.memLp _).mono_measure (localMeasure_mono hac hdb))

theorem restricted_criticalGradient_norm_eq {a b c d : ℝ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (q : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ‖criticalGradient (intervalMeasure c d) j (restrictPath hac hcd hdb q)‖ =
      lpNorm (toLocalLp (hac.trans (hcd.trans hdb)) 10
        (criticalGradient (intervalMeasure a b) j q)) 10 (localMeasure c d) := by
  exact (congrArg norm (restrictPath_gradient hac hcd hdb q j)).trans
    (restrictIntervalLp_norm_eq_lpNorm 10 hac hcd hdb (criticalGradient _ j q))

#print axioms restrictIntervalLp_norm_eq_lpNorm
#print axioms pathValueLp_restrict
#print axioms restricted_pathValueSize_eq
#print axioms restricted_criticalGradient_norm_eq
end HartreeF.ActualPathPartitions
