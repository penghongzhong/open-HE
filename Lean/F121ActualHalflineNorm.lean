import F121NativeHalflineSize

/-! The actual L10_x value of the energy state, and its genuine L10_t norm
on a native half-line. No finite global L10 witness is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121ActualNorm
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalSourceBounds
  SobolevStretch StationarySelfTest MaximalTrajectory ActualSTail Paper121Halfline
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath LocalMildTrajectory.path

/-- Spatial L10 realization wherever the actual energy value lies in L10.
The fallback is irrelevant almost everywhere on every native compact interval. -/
def actualValue (u : EnergyState) : ValueSpace := by
  classical
  exact if h : MemLp (energyValue u) 10 (volume : Measure Space) then
    h.toLp (energyValue u)
  else 0

theorem actualValue_coeFn_of_mem (u : EnergyState)
    (h : MemLp (energyValue u) 10 (volume : Measure Space)) :
    (actualValue u : Space → ℂ) =ᵐ[volume] energyValue u := by
  classical
  rw [actualValue, dite_eq_left h]
  exact h.coeFn_toLp

theorem actualValue_compact (hDensity : OrdinaryH1Density)
    {K alpha kernel s a b : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (hab : a ≤ b)
    (hI : Icc a b ⊆ U.domain) :
    ∀ᵐ t ∂localMeasure a b,
      (actualValue (U.state t) : Space → ℂ) =ᵐ[volume] energyValue (U.state t) := by
  filter_upwards [globalPathValue_actual hDensity hSob U hab hI] with t ht
  apply actualValue_coeFn_of_mem
  exact (memLp_congr_ae ht).mp
    (Lp.memLp (globalPathValue hDensity hSob hab (U.path hab hI) t))

/-- Exact compact norm identity for an arbitrary time function into L10_x;
there is no global L10_t membership premise. -/
theorem actual_pathValueSize_eq_function (hDensity : OrdinaryH1Density)
    {K alpha kernel s a b : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (hab : a ≤ b)
    (hI : Icc a b ⊆ U.domain) (F : ℝ → ValueSpace)
    (hF : ∀ᵐ t ∂localMeasure a b,
      (F t : Space → ℂ) =ᵐ[volume] energyValue (U.state t)) :
    pathValueSize (intervalMeasure a b) (U.path hab hI) =
      eLpNorm F 10 (localMeasure a b) := by
  let G := globalPathValue hDensity hSob hab (U.path hab hI)
  have hG := globalPathValue_actual hDensity hSob U hab hI
  have hGF : (G : ℝ → ValueSpace) =ᵐ[localMeasure a b] F := by
    filter_upwards [hG, hF] with t hg hf
    exact Lp.ext (hg.trans hf.symm)
  exact (actual_pathValueSize_eq hDensity hSob U hab hI G hG).trans
    (eLpNorm_congr_ae hGF)

theorem nativeSAfter_le_actual_halfline_norm (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (a : ℝ) :
    nativeSAfter U a ≤ eLpNorm (fun t => actualValue (U.state t)) 10
      (volume.restrict (U.domain ∩ Ici a)) := by
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  apply iSup_le
  intro hI
  rw [actual_pathValueSize_eq_function hDensity hSob U hab hI
    (fun t => actualValue (U.state t)) (actualValue_compact hDensity hSob U hab hI)]
  apply eLpNorm_mono_measure
  exact Measure.restrict_mono_set _ (fun _ ht => ⟨hI ht, ht.1⟩)

theorem nativeSBefore_le_actual_halfline_norm (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (a : ℝ) :
    nativeSBefore U a ≤ eLpNorm (fun t => actualValue (U.state t)) 10
      (volume.restrict (U.domain ∩ Iic a)) := by
  apply iSup_le
  intro b
  apply iSup_le
  intro hba
  apply iSup_le
  intro hI
  rw [actual_pathValueSize_eq_function hDensity hSob U hba hI
    (fun t => actualValue (U.state t)) (actualValue_compact hDensity hSob U hba hI)]
  apply eLpNorm_mono_measure
  exact Measure.restrict_mono_set _ (fun _ ht => ⟨hI ht, ht.2⟩)

theorem actual_halfline_norms_eq_top (hDensity : OrdinaryH1Density)
    {K alpha kernel s a : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f)
    (h : nativeSAfter U a = ∞ ∧ nativeSBefore U a = ∞) :
    eLpNorm (fun t => actualValue (U.state t)) 10
        (volume.restrict (U.domain ∩ Ici a)) = ∞ ∧
      eLpNorm (fun t => actualValue (U.state t)) 10
        (volume.restrict (U.domain ∩ Iic a)) = ∞ := by
  constructor
  · apply top_unique
    rw [← h.1]
    exact nativeSAfter_le_actual_halfline_norm hDensity hSob U a
  · apply top_unique
    rw [← h.2]
    exact nativeSBefore_le_actual_halfline_norm hDensity hSob U a

end HartreeF.Paper121ActualNorm
