import FActualBilateralPathTools
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Monotonicity and two-interval bounds for the actual compact S norm. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.ActualSIntervalBounds
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalSourceBounds
open SobolevStretch StationarySelfTest MaximalTrajectory ActualSTail
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath LocalMildTrajectory.path

private theorem interval_eLpNorm_split (F : GlobalValueSpace) {a b c : ℝ} :
    eLpNorm F 10 (localMeasure a b) ≤
      eLpNorm F 10 (localMeasure a c) + eLpNorm F 10 (localMeasure c b) := by
  classical
  have heq : (F : ℝ → ValueSpace) =
      (Iic c).indicator F + (Iic c)ᶜ.indicator F := by
    funext t
    by_cases ht : t ∈ Iic c <;> simp [ht]
  have hL : eLpNorm ((Iic c).indicator F) 10 (localMeasure a b) ≤
      eLpNorm F 10 (localMeasure a c) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic.nullMeasurableSet]
    apply eLpNorm_mono_measure
    change (volume.restrict (Icc a b)).restrict (Iic c) ≤ volume.restrict (Icc a c)
    rw [Measure.restrict_restrict measurableSet_Iic]
    exact Measure.restrict_mono_set _ (fun _ ht => ⟨ht.2.1, ht.1⟩)
  have hR : eLpNorm ((Iic c)ᶜ.indicator F) 10 (localMeasure a b) ≤
      eLpNorm F 10 (localMeasure c b) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Iic.compl.nullMeasurableSet]
    apply eLpNorm_mono_measure
    change (volume.restrict (Icc a b)).restrict (Iic c)ᶜ ≤ volume.restrict (Icc c b)
    rw [Measure.restrict_restrict measurableSet_Iic.compl]
    exact Measure.restrict_mono_set _ (fun _ ht => ⟨(lt_of_not_ge ht.1).le, ht.2.2⟩)
  calc
    _ = eLpNorm ((Iic c).indicator F + (Iic c)ᶜ.indicator F) 10 (localMeasure a b) :=
      congrArg (fun f : ℝ → ValueSpace => eLpNorm f 10 (localMeasure a b)) heq
    _ ≤ eLpNorm ((Iic c).indicator F) 10 (localMeasure a b) +
        eLpNorm ((Iic c)ᶜ.indicator F) 10 (localMeasure a b) := eLpNorm_add_le (by norm_num)
    _ ≤ _ := add_le_add hL hR

theorem actual_snorm_mono (hDensity : OrdinaryH1Density) {K alpha kernel s a b c d : ℝ}
    (hSob : OrdinarySobolev K) {f : EnergyState} (U : LocalMildTrajectory alpha kernel s f)
    (hab : a ≤ b) (hI : Icc a b ⊆ U.domain)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (hJ : Icc c d ⊆ U.domain) :
    pathValueSize (intervalMeasure c d) (U.path hcd hJ) ≤
      pathValueSize (intervalMeasure a b) (U.path hab hI) := by
  let F := globalPathValue hDensity hSob hab (U.path hab hI)
  have hF := globalPathValue_actual hDensity hSob U hab hI
  rw [actual_pathValueSize_eq hDensity hSob U hcd hJ F
    (ae_mono (localMeasure_mono hac hdb) hF),
    actual_pathValueSize_eq hDensity hSob U hab hI F hF]
  exact eLpNorm_mono_measure F (localMeasure_mono hac hdb)

theorem actual_snorm_split_le (hDensity : OrdinaryH1Density) {K alpha kernel s a b c : ℝ}
    (hSob : OrdinarySobolev K) {f : EnergyState} (U : LocalMildTrajectory alpha kernel s f)
    (hac : a ≤ c) (hcb : c ≤ b) (hI : Icc a b ⊆ U.domain)
    (hL : Icc a c ⊆ U.domain) (hR : Icc c b ⊆ U.domain) :
    pathValueSize (intervalMeasure a b) (U.path (hac.trans hcb) hI) ≤
      pathValueSize (intervalMeasure a c) (U.path hac hL) +
      pathValueSize (intervalMeasure c b) (U.path hcb hR) := by
  let F := globalPathValue hDensity hSob (hac.trans hcb) (U.path (hac.trans hcb) hI)
  have hF := globalPathValue_actual hDensity hSob U (hac.trans hcb) hI
  rw [actual_pathValueSize_eq hDensity hSob U (hac.trans hcb) hI F hF,
    actual_pathValueSize_eq hDensity hSob U hac hL F
      (ae_mono (localMeasure_mono le_rfl hcb) hF),
    actual_pathValueSize_eq hDensity hSob U hcb hR F
      (ae_mono (localMeasure_mono hac le_rfl) hF)]
  exact interval_eLpNorm_split F

end HartreeF.ActualSIntervalBounds
