import F121CriticalKineticBounds
import FActualSIntervalBounds

/-! Native half-line scattering sizes, defined by the supremum of genuine
compact-path L10 norms. Finiteness is independent of the native cut time.
No global lifespan, mass bound, or chosen spacetime representative is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121Halfline
open EnergySpace CriticalPathSpace CriticalSourceBounds MaximalTrajectory
  SobolevStretch StationarySelfTest BilateralPathTools ActualSIntervalBounds
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath LocalMildTrajectory.path

/-- A finite forward bound at one native cut gives one at any other cut.
The finite compact bridge is kept explicitly. -/
theorem finite_after_at_of_finite_after_at (hDensity : OrdinaryH1Density)
    {K alpha kernel s a c : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (ha : a ∈ U.domain) (hc : c ∈ U.domain)
    (hfinite : ∃ M : ℝ≥0, ActualSTail.UniformSNormAfter U c M) :
    ∃ M : ℝ≥0, ActualSTail.UniformSNormAfter U a M := by
  obtain ⟨M, hM⟩ := hfinite
  by_cases hac : a ≤ c
  · have hAC : Icc a c ⊆ U.domain := U.domain_connected.out' ha hc
    let L : ℝ≥0 := ⟨graphSConstant K * ‖U.path hac hAC‖,
      mul_nonneg (graphSConstant_nonneg hSob) (norm_nonneg _)⟩
    have hL : pathValueSize (intervalMeasure a c) (U.path hac hAC) ≤ (L : ℝ≥0∞) :=
      (pathValueSize_le_graph hDensity hSob _).trans_eq
        (show ENNReal.ofReal (L : ℝ) = (L : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
    refine ⟨L + M, ?_⟩
    intro b hab hAB
    rw [ENNReal.coe_add]
    by_cases hbc : b ≤ c
    · exact ((actual_snorm_mono hDensity hSob U hac hAC le_rfl hab hbc hAB).trans hL).trans
        le_self_add
    · have hcb : c ≤ b := (lt_of_not_ge hbc).le
      have hCB : Icc c b ⊆ U.domain :=
        U.domain_connected.out' hc (hAB ⟨hab, le_rfl⟩)
      exact (actual_snorm_split_le hDensity hSob U hac hcb hAB hAC hCB).trans
        (add_le_add hL (hM b hcb hCB))
  · have hca : c ≤ a := (lt_of_not_ge hac).le
    refine ⟨M, ?_⟩
    intro b hab hAB
    have hCB : Icc c b ⊆ U.domain :=
      U.domain_connected.out' hc (hAB ⟨hab, le_rfl⟩)
    exact (actual_snorm_mono hDensity hSob U (hca.trans hab) hCB hca hab le_rfl hAB).trans
      (hM b (hca.trans hab) hCB)

/-- The backward counterpart, retaining the compact bridge to the new cut. -/
theorem finite_before_at_of_finite_before_at (hDensity : OrdinaryH1Density)
    {K alpha kernel s a c : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (ha : a ∈ U.domain) (hc : c ∈ U.domain)
    (hfinite : ∃ M : ℝ≥0, ActualInfiniteLeftSTail.UniformSNormBefore U c M) :
    ∃ M : ℝ≥0, ActualInfiniteLeftSTail.UniformSNormBefore U a M := by
  obtain ⟨M, hM⟩ := hfinite
  by_cases hca : c ≤ a
  · have hCA : Icc c a ⊆ U.domain := U.domain_connected.out' hc ha
    let L : ℝ≥0 := ⟨graphSConstant K * ‖U.path hca hCA‖,
      mul_nonneg (graphSConstant_nonneg hSob) (norm_nonneg _)⟩
    have hL : pathValueSize (intervalMeasure c a) (U.path hca hCA) ≤ (L : ℝ≥0∞) :=
      (pathValueSize_le_graph hDensity hSob _).trans_eq
        (show ENNReal.ofReal (L : ℝ) = (L : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal)
    refine ⟨M + L, ?_⟩
    intro b hba hBA
    rw [ENNReal.coe_add]
    by_cases hcb : c ≤ b
    · exact ((actual_snorm_mono hDensity hSob U hca hCA hcb hba le_rfl hBA).trans hL).trans
        le_add_self
    · have hbc : b ≤ c := (lt_of_not_ge hcb).le
      have hBC : Icc b c ⊆ U.domain :=
        U.domain_connected.out' (hBA ⟨le_rfl, hba⟩) hc
      exact (actual_snorm_split_le hDensity hSob U hbc hca hBA hBC hCA).trans
        (add_le_add (hM b hbc hBC) hL)
  · have hac : a ≤ c := (lt_of_not_ge hca).le
    refine ⟨M, ?_⟩
    intro b hba hBA
    have hBC : Icc b c ⊆ U.domain :=
      U.domain_connected.out' (hBA ⟨le_rfl, hba⟩) hc
    exact (actual_snorm_mono hDensity hSob U (hba.trans hac) hBC le_rfl hba hac hBA).trans
      (hM b (hba.trans hac) hBC)

def nativeSAfter {alpha kernel s : ℝ} {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (a : ℝ) : ℝ≥0∞ :=
  ⨆ (b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ U.domain),
    pathValueSize (intervalMeasure a b) (U.path hab hI)

def nativeSBefore {alpha kernel s : ℝ} {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (a : ℝ) : ℝ≥0∞ :=
  ⨆ (b : ℝ) (hba : b ≤ a) (hI : Icc b a ⊆ U.domain),
    pathValueSize (intervalMeasure b a) (U.path hba hI)

theorem nativeSAfter_eq_top_of_bad (hDensity : OrdinaryH1Density)
    {K alpha kernel s a : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (ha : a ∈ U.domain)
    (hbad : ¬ ActualScattering.FiniteSAfter U) : nativeSAfter U a = ∞ := by
  by_contra hne
  have hfinite : ∃ M : ℝ≥0, ActualSTail.UniformSNormAfter U a M := by
    refine ⟨(nativeSAfter U a).toNNReal, ?_⟩
    intro b hab hI
    rw [ENNReal.coe_toNNReal hne]
    exact le_iSup_of_le b (le_iSup_of_le hab (le_iSup_of_le hI le_rfl))
  exact hbad (finite_after_at_of_finite_after_at hDensity hSob U U.center_mem ha hfinite)

theorem nativeSBefore_eq_top_of_bad (hDensity : OrdinaryH1Density)
    {K alpha kernel s a : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (ha : a ∈ U.domain)
    (hbad : ¬ ActualLeftScattering.FiniteSBefore U) : nativeSBefore U a = ∞ := by
  by_contra hne
  have hfinite : ∃ M : ℝ≥0, ActualInfiniteLeftSTail.UniformSNormBefore U a M := by
    refine ⟨(nativeSBefore U a).toNNReal, ?_⟩
    intro b hba hI
    rw [ENNReal.coe_toNNReal hne]
    exact le_iSup_of_le b (le_iSup_of_le hba (le_iSup_of_le hI le_rfl))
  exact hbad (finite_before_at_of_finite_before_at hDensity hSob U U.center_mem ha hfinite)

end HartreeF.Paper121Halfline
