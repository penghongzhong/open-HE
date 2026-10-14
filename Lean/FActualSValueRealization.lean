import FLocalMildTrajectory
import FJointLpRealization
import FCriticalPathQuantitativeNorms
import FEndpointTimeExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology

namespace HartreeF.ActualSTail
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalJointSources
open CriticalSourceBounds TimeHolder SobolevStretch StationarySelfTest MaximalTrajectory
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields

local instance : Fact ((10 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

abbrev ValueSpace := Lp ℂ 10 (volume : Measure Space)
abbrev GlobalValueSpace := Lp ValueSpace 10 (volume : Measure ℝ)

/-- The actual value field of a compact critical path, realized in L10_t L10_x. -/
def pathValueLp (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {a b : ℝ} (u : CriticalPath (intervalMeasure a b)) :
    Lp ValueSpace 10 (intervalMeasure a b) :=
  jointLpRealization (intervalMeasure a b) volume 10 10
    (fun z => (jointFields (intervalMeasure a b) u).u z.1 z.2)
    (jointFields (intervalMeasure a b) u).joint_u.aestronglyMeasurable
    (joint_value_critical (intervalMeasure a b) hDensity hSob u).1
    (joint_value_critical (intervalMeasure a b) hDensity hSob u).2

theorem pathValueLp_coeFn (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {a b : ℝ} (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂intervalMeasure a b, (pathValueLp hDensity hSob u t : Space → ℂ) =ᵐ[volume]
      energyValue (energyPath (intervalMeasure a b) u t) := by
  have h : ∀ᵐ t ∂intervalMeasure a b,
      (pathValueLp hDensity hSob u t : Space → ℂ) =ᵐ[volume]
        (jointFields (intervalMeasure a b) u).u t :=
    jointLpRealization_coeFn (intervalMeasure a b) volume 10 10
    (fun z => (jointFields (intervalMeasure a b) u).u z.1 z.2)
    (jointFields (intervalMeasure a b) u).joint_u.aestronglyMeasurable
    (joint_value_critical (intervalMeasure a b) hDensity hSob u).1
    (joint_value_critical (intervalMeasure a b) hDensity hSob u).2
  filter_upwards [h, (jointFields (intervalMeasure a b) u).slice_eq] with t ht hs
  exact Filter.EventuallyEq.trans ht hs.1

theorem pathValueLp_norm (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {a b : ℝ} (u : CriticalPath (intervalMeasure a b)) :
    ‖pathValueLp hDensity hSob u‖ = (pathValueSize (intervalMeasure a b) u).toReal :=
  jointLpRealization_norm (intervalMeasure a b) volume 10 10
    (fun z => (jointFields (intervalMeasure a b) u).u z.1 z.2)
    (jointFields (intervalMeasure a b) u).joint_u.aestronglyMeasurable
    (joint_value_critical (intervalMeasure a b) hDensity hSob u).1
    (joint_value_critical (intervalMeasure a b) hDensity hSob u).2

theorem pathValueLp_enorm (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {a b : ℝ} (u : CriticalPath (intervalMeasure a b)) :
    ‖pathValueLp hDensity hSob u‖ₑ = pathValueSize (intervalMeasure a b) u :=
  jointLpRealization_enorm (intervalMeasure a b) volume 10 10
    (fun z => (jointFields (intervalMeasure a b) u).u z.1 z.2)
    (jointFields (intervalMeasure a b) u).joint_u.aestronglyMeasurable
    (joint_value_critical (intervalMeasure a b) hDensity hSob u).1
    (joint_value_critical (intervalMeasure a b) hDensity hSob u).2

/-- Exponent-10 extension by zero, with the original local representatives retained. -/
def extendValueLp {a b : ℝ} (f : Lp ValueSpace 10 (localMeasure a b)) : GlobalValueSpace :=
  ((memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (Lp.memLp f)).toLp
    ((Set.Icc a b).indicator f)

theorem extendValueLp_coeFn {a b : ℝ} (f : Lp ValueSpace 10 (localMeasure a b)) :
    (extendValueLp f : ℝ → ValueSpace) =ᵐ[volume] (Set.Icc a b).indicator f :=
  ((memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (Lp.memLp f)).coeFn_toLp

theorem extendValueLp_restrict_coeFn {a b : ℝ}
    (f : Lp ValueSpace 10 (localMeasure a b)) :
    (extendValueLp f : ℝ → ValueSpace) =ᵐ[localMeasure a b] f := by
  filter_upwards [ae_restrict_of_ae (extendValueLp_coeFn f), ae_restrict_mem measurableSet_Icc]
    with t ht hm
  simpa only [Set.indicator_of_mem hm] using ht

theorem extendValueLp_norm {a b : ℝ} (f : Lp ValueSpace 10 (localMeasure a b)) :
    ‖extendValueLp f‖ = ‖f‖ := by
  rw [extendValueLp, Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet, Lp.norm_def]

def globalPathValue (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b)
    (u : CriticalPath (intervalMeasure a b)) : GlobalValueSpace :=
  extendValueLp (toLocalLp hab 10 (pathValueLp hDensity hSob u))

theorem globalPathValue_norm (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b)
    (u : CriticalPath (intervalMeasure a b)) :
    ‖globalPathValue hDensity hSob hab u‖ = (pathValueSize (intervalMeasure a b) u).toReal := by
  rw [globalPathValue, extendValueLp_norm, toLocalLp_norm, pathValueLp_norm]

theorem globalPathValue_support (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b)
    (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂volume, t ∉ Set.Icc a b → globalPathValue hDensity hSob hab u t = 0 := by
  filter_upwards [extendValueLp_coeFn (toLocalLp hab 10 (pathValueLp hDensity hSob u))]
    with t ht
  intro htn
  simpa only [globalPathValue, Set.indicator_of_notMem htn] using ht

theorem globalPathValue_actual (hDensity : OrdinaryH1Density) {K alpha kernel s0 a b : ℝ}
    (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ U.domain) :
    ∀ᵐ t ∂localMeasure a b,
      (globalPathValue hDensity hSob hab (U.path hab hI) t : Space → ℂ) =ᵐ[volume]
        energyValue (U.state t) := by
  let u := U.path hab hI
  filter_upwards [extendValueLp_restrict_coeFn (toLocalLp hab 10 (pathValueLp hDensity hSob u)),
    toLocalLp_coeFn hab 10 (pathValueLp hDensity hSob u),
    ae_clamp hab (pathValueLp_coeFn hDensity hSob u), ae_restrict_mem measurableSet_Icc]
    with t he hl hv ht
  change (extendValueLp (toLocalLp hab 10 (pathValueLp hDensity hSob u)) t : Space → ℂ) =ᵐ[volume] _
  rw [he, hl]
  have hs : energyPath (intervalMeasure a b) u (Set.projIcc a b hab t) = U.state t := by
    rw [U.path_agrees hab hI, Set.projIcc_of_mem hab ht]
  exact hv.trans (Eventually.of_forall fun x => congrArg (fun z : EnergyState => energyValue z x) hs)

/-- On any actual compact interval, any value realization of the same states
has exactly the actual S norm. The identity includes singleton intervals. -/
theorem actual_pathValueSize_eq (hDensity : OrdinaryH1Density) {K alpha kernel s0 a b : ℝ}
    (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel s0 u0) (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ U.domain) (F : GlobalValueSpace)
    (hF : ∀ᵐ t ∂localMeasure a b, (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t)) :
    pathValueSize (intervalMeasure a b) (U.path hab hI) =
      eLpNorm F 10 (localMeasure a b) := by
  let u := U.path hab hI
  let v := toLocalLp hab 10 (pathValueLp hDensity hSob u)
  have hv : (v : ℝ → ValueSpace) =ᵐ[localMeasure a b] F := by
    filter_upwards [extendValueLp_restrict_coeFn v,
      globalPathValue_actual hDensity hSob U hab hI, hF] with t he hg hf
    apply Lp.ext
    have hg' : (v t : Space → ℂ) =ᵐ[volume] energyValue (U.state t) := by
      change (extendValueLp v t : Space → ℂ) =ᵐ[volume] _ at hg
      rw [he] at hg
      exact hg
    exact hg'.trans hf.symm
  calc
    pathValueSize (intervalMeasure a b) u = ‖pathValueLp hDensity hSob u‖ₑ :=
      (pathValueLp_enorm hDensity hSob u).symm
    _ = ‖v‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact congrArg ENNReal.ofReal (toLocalLp_norm hab 10 (pathValueLp hDensity hSob u)).symm
    _ = eLpNorm v 10 (localMeasure a b) := Lp.enorm_def v
    _ = eLpNorm F 10 (localMeasure a b) := eLpNorm_congr_ae hv

end HartreeF.ActualSTail
