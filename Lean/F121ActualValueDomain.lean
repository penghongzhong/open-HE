import F121ActualHalflineNorm
import FIntervalExhaustionGeometry

/-! Actual spatial representatives on the whole native lifespan, and the
literal mixed norm used by the manuscript. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121ActualDomain
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalSourceBounds
  SobolevStretch StationarySelfTest MaximalTrajectory ActualSTail
  Paper121Halfline Paper121ActualNorm IntervalNormExhaustion
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath LocalMildTrajectory.path

theorem actualValue_domain (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) :
    ∀ᵐ t ∂volume.restrict U.domain,
      (actualValue (U.state t) : Space → ℂ) =ᵐ[volume] energyValue (U.state t) := by
  obtain ⟨a, b, _ha, _hb, hab, hsub, hcover⟩ :=
    exists_centered_interval_exhaustion U.domain U.domain_connected U.center_mem
  have hall : ∀ᵐ t ∂(volume : Measure ℝ), ∀ n,
      t ∈ Icc (a n) (b n) →
      (actualValue (U.state t) : Space → ℂ) =ᵐ[volume] energyValue (U.state t) :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_Icc).mp
      (actualValue_compact hDensity hSob U ((hab n).2.2.1.trans (hab n).2.2.2) (hsub n))
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem U.domain_open.measurableSet]
    with t ht hmem
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover.symm ▸ hmem)
  exact ht n hn

theorem actualValue_aestronglyMeasurable (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) :
    AEStronglyMeasurable (fun t => actualValue (U.state t))
      (volume.restrict U.domain) := by
  obtain ⟨a, b, _ha, _hb, hab, hsub, hcover⟩ :=
    exists_centered_interval_exhaustion U.domain U.domain_connected U.center_mem
  rw [← hcover]
  apply AEStronglyMeasurable.iUnion
  intro n
  let habn := (hab n).2.2.1.trans (hab n).2.2.2
  let G := globalPathValue hDensity hSob habn (U.path habn (hsub n))
  have hEq : (G : ℝ → ValueSpace) =ᵐ[localMeasure (a n) (b n)]
      (fun t => actualValue (U.state t)) := by
    filter_upwards [globalPathValue_actual hDensity hSob U habn (hsub n),
      actualValue_compact hDensity hSob U habn (hsub n)] with t hg hv
    exact Lp.ext (hg.trans hv.symm)
  exact ((Lp.aestronglyMeasurable G).mono_measure Measure.restrict_le_self).congr hEq

theorem actual_mixedNorm_eq_value_norm (hDensity : OrdinaryH1Density)
    {K alpha kernel s : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (I : Set ℝ) (hI : I ⊆ U.domain) :
    TimeHolder.mixedNorm (volume.restrict I) volume 10 10
        (fun t => energyValue (U.state t)) =
      eLpNorm (fun t => actualValue (U.state t)) 10 (volume.restrict I) := by
  have hmeasure : (volume : Measure ℝ).restrict I ≤ volume.restrict U.domain :=
    Measure.restrict_mono_set _ hI
  calc
    _ = eLpNorm (fun t => ‖actualValue (U.state t)‖ₑ) 10 (volume.restrict I) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_mono hmeasure (actualValue_domain hDensity hSob U)] with t ht
      exact (eLpNorm_congr_ae ht.symm).trans (Lp.enorm_def _).symm
    _ = _ := eLpNorm_enorm _
      ((actualValue_aestronglyMeasurable hDensity hSob U).mono_measure hmeasure)

theorem actual_mixed_halfline_norms_eq_top (hDensity : OrdinaryH1Density)
    {K alpha kernel s a : ℝ} (hSob : OrdinarySobolev K) {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f)
    (h : nativeSAfter U a = ∞ ∧ nativeSBefore U a = ∞) :
    TimeHolder.mixedNorm (volume.restrict (U.domain ∩ Ici a)) volume 10 10
        (fun t => energyValue (U.state t)) = ∞ ∧
      TimeHolder.mixedNorm (volume.restrict (U.domain ∩ Iic a)) volume 10 10
        (fun t => energyValue (U.state t)) = ∞ := by
  rw [actual_mixedNorm_eq_value_norm hDensity hSob U _ inter_subset_left,
    actual_mixedNorm_eq_value_norm hDensity hSob U _ inter_subset_left]
  exact actual_halfline_norms_eq_top hDensity hSob U h

end HartreeF.Paper121ActualDomain
