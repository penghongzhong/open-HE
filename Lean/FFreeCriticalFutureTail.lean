import FLocalFreePathCaps
import FiniteLpTail

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.WaveTerminal
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport TimeHolder
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain CutoffApproximation
attribute [local irreducible] energySubmodule criticalPathSubmodule freeCriticalPath freeJoint
  energyPath criticalGradient

/-- The actual free-gradient W tail vanishes for arbitrary homogeneous data.
Only the gradient coordinates, which already belong to L2, enter Strichartz. -/
theorem free_gradient_future_tail_tendsto {Ch : ℝ}
    (hfree : OrdinaryHomogeneousStrichartz Ch) (f : EnergyState) (j : Fin 3) :
    Tendsto (fun n : ℕ => mixedNorm (volume.restrict (Ici (n:ℝ))) volume
      10 criticalExponent (freeJoint (energyGradient j f))) atTop (𝓝 0) := by
  let d := freeJoint (energyGradient j f)
  let g := fun t => (eLpNorm (d t) criticalExponent volume).toReal
  have hf : mixedNorm volume volume 10 criticalExponent d≠∞ :=
    freeJoint_mixedNorm_finite hfree (energyGradient j f)
  have hm : AEStronglyMeasurable (fun t => eLpNorm (d t) criticalExponent volume) volume :=
    aestronglyMeasurable_of_eLpNorm_ne_top hf
  have hs : ∀ᵐ t ∂(volume : Measure ℝ), eLpNorm (d t) criticalExponent volume≠∞ :=
    (freeJoint_ae_critical_memLp hfree (energyGradient j f)).mono fun _ ht => ht.ne
  have hg : MemLp g 10 volume := by
    change eLpNorm g 10 volume<∞
    rw [← finite_extended_norm_bridge volume 10 _ hm hs]
    exact lt_top_iff_ne_top.mpr hf
  have hempty : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᶠ n : ℕ in atTop, t∉Ici (n:ℝ) := by
    filter_upwards [] with t
    obtain ⟨N,hN⟩ := exists_nat_gt t
    filter_upwards [eventually_ge_atTop N] with n hn
    exact not_le_of_gt (hN.trans_le (Nat.cast_le.mpr hn))
  have ht := tendsto_eLpNorm_indicator_eventually_empty hg
    (by norm_num : (10:ℝ≥0∞)≠0) (by norm_num : (10:ℝ≥0∞)≠∞)
    (fun n => measurableSet_Ici (a := (n:ℝ))) hempty
  have he (n : ℕ) : mixedNorm (volume.restrict (Ici (n:ℝ))) volume 10 criticalExponent d=
      eLpNorm ((Ici (n:ℝ)).indicator g) 10 volume := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici.nullMeasurableSet]
    exact finite_extended_norm_bridge _ 10 _ hm.restrict (ae_restrict_of_ae hs)
  exact ht.congr' (Eventually.of_forall fun n => (he n).symm)

/-- One tail start controls every later compact interval, simultaneously for
all three exact free-gradient coordinates. -/
theorem exists_freeCriticalPath_future_small (hDensity : OrdinaryH1Density)
    {K Ch : ℝ} (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (f : EnergyState) {eta : ℝ} (heta : 0<eta) :
    ∃ T : ℝ, ∀ A R : ℝ, T≤A → A≤R → ∀ j : Fin 3,
      ‖criticalGradient _ j (freeCriticalPath hDensity hSob hfree A R f)‖≤eta := by
  have hsmall : ∀ j : Fin 3, ∀ᶠ n : ℕ in atTop,
      mixedNorm (volume.restrict (Ici (n:ℝ))) volume 10 criticalExponent
        (freeJoint (energyGradient j f))<ENNReal.ofReal eta := by
    intro j
    exact (free_gradient_future_tail_tendsto hfree f j).eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.mpr heta))
  obtain ⟨N,hN⟩ := (Filter.eventually_all.mpr hsmall).exists
  refine ⟨(N:ℝ),?_⟩
  intro A R hNA _ j
  apply (ENNReal.ofReal_le_ofReal_iff heta.le).mp
  rw [ofReal_norm,freeCriticalPath_gradient_eq_restrict]
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume
    (show Icc A R⊆Ici (N:ℝ) from fun _ ht => hNA.trans ht.1))).trans (hN j).le

end HartreeF.WaveTerminal
