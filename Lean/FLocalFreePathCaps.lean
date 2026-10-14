import FActualDuhamelCoordinateBounds
import FFourInputLocalization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace TimeHolder ActualStrichartz
open SobolevStretch StationarySelfTest
attribute [local irreducible] freeCriticalPath criticalPathOfGlobalFields
  freeEnergyState freeJoint

/-- The subtype time norm equals the ambient norm restricted to the same interval. -/
theorem interval_mixedNorm_eq_restrict (a b : ℝ) (p q : ℝ≥0∞)
    (f : ℝ → Space → ℂ) :
    mixedNorm (intervalMeasure a b) volume p q (fun t => f (t : ℝ)) =
      mixedNorm (volume.restrict (Set.Icc a b)) volume p q f := by
  have he := (MeasurableEmbedding.subtype_coe (show MeasurableSet (Set.Icc a b) from
    measurableSet_Icc)).eLpNorm_map_measure
    (g := fun t => eLpNorm (f t) q volume) (p := p) (μ := intervalMeasure a b)
  rw [(inclusion_measurePreserving a b).map_eq] at he
  exact he.symm

/-- Graph coordinates retain the exact restricted norm of the actual joint field. -/
theorem criticalPathOfGlobalFields_gradient_eq_restrict (a b : ℝ)
    (g : ℝ → EnergyState) (hg : Continuous g) (d : Fin 3 → ℝ → Space → ℂ)
    (hdm : ∀ j, StronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2))
    (hdf : ∀ j, mixedNorm volume volume 10 criticalExponent (d j) ≠ ∞)
    (hd : ∀ j, ∀ᵐ t ∂(volume : Measure ℝ), d j t =ᵐ[volume] energyGradient j (g t))
    (j : Fin 3) :
    ‖criticalGradient _ j (criticalPathOfGlobalFields a b g hg d hdm hdf hd)‖ₑ =
      mixedNorm (volume.restrict (Set.Icc a b)) volume 10 criticalExponent (d j) := by
  rw [← criticalGradient_eLpNorm, ← interval_mixedNorm_eq_restrict]
  apply eLpNorm_congr_ae
  have hdi := (inclusion_measurePreserving a b).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (hd j))
  filter_upwards [hdi] with t ht
  rw [criticalPathOfGlobalFields_energy]
  exact (eLpNorm_congr_ae ht).symm

/-- Exact local coordinate norm of the literal Fourier free path. -/
theorem freeCriticalPath_gradient_eq_restrict (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (a b : ℝ) (u : EnergyState) (j : Fin 3) :
    ‖criticalGradient _ j (freeCriticalPath hDensity hSob h a b u)‖ₑ =
      mixedNorm (volume.restrict (Set.Icc a b)) volume 10 criticalExponent
        (freeJoint (energyGradient j u)) := by
  unfold freeCriticalPath
  exact criticalPathOfGlobalFields_gradient_eq_restrict a b _ _ _ _ _ _ j

/-- The shifted free path takes the prescribed datum at the left endpoint. -/
theorem shiftedFreeCriticalPath_initial (hDensity : OrdinaryH1Density) {K C a b : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (hab : a ≤ b) (u0 : EnergyState) :
    energyPath _ (freeCriticalPath hDensity hSob h a b
      (freeEnergyState hDensity hSob (-a) u0)) ⟨a, le_rfl, hab⟩ = u0 := by
  rw [freeCriticalPath_energy]
  exact freeEnergyState_inverse hDensity hSob a u0

/-- The uniform energy cap has a single Sobolev constant, by the group law. -/
theorem shiftedFreeCriticalPath_energy_norm_le (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (a b : ℝ) (u0 : EnergyState) :
    ‖energyPath _ (freeCriticalPath hDensity hSob h a b
      (freeEnergyState hDensity hSob (-a) u0))‖ ≤
      (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) * ‖u0‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  rw [freeCriticalPath_energy, ← freeEnergyState_add_time]
  exact freeEnergyState_norm_bound hDensity hSob ((t : ℝ) + -a) u0

/-- Three finite Fourier gradient fields share one arbitrarily small time ball. -/
theorem freeJoint_coordinates_local_smallness {C : ℝ}
    (h : OrdinaryHomogeneousStrichartz C) (u : EnergyState)
    (a eta : ℝ) (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∀ j : Fin 3,
      mixedNorm (volume.restrict (Metric.ball a r)) volume 10 criticalExponent
        (freeJoint (energyGradient j u)) ≤ ENNReal.ofReal eta := by
  let d := fun j : Fin 3 => freeJoint (energyGradient j u)
  have hf (j : Fin 3) : mixedNorm volume volume 10 criticalExponent (d j) ≠ ∞ :=
    freeJoint_mixedNorm_finite h (energyGradient j u)
  obtain ⟨r, hr, hzero, hrest⟩ := finite_four_mixedNorm_exists_small_ball
    volume le_rfl volume criticalExponent criticalExponent (d 0) (d 0) (d 1) (d 2)
    (hf 0) (hf 0) (hf 1) (hf 2) a eta heta
  refine ⟨r, hr, ?_⟩
  intro j
  fin_cases j
  · exact le_trans le_self_add hzero
  · exact le_trans le_self_add hrest
  · exact le_trans le_add_self hrest

set_option maxHeartbeats 200000 in
set_option diagnostics true in
/-- Every datum has a positive forward compact interval on which all three
actual free critical coordinates are arbitrarily small. Only finiteness from
the numerical homogeneous Strichartz estimate enters time localization. -/
theorem exists_shiftedFreeCriticalPath_small (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (a : ℝ) (u0 : EnergyState) (eta : ℝ) (heta : 0 < eta) :
    ∃ b : ℝ, a < b ∧
      ‖energyPath _ (freeCriticalPath hDensity hSob h a b
        (freeEnergyState hDensity hSob (-a) u0))‖ ≤
        (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) * ‖u0‖ ∧
      ∀ j : Fin 3, ‖criticalGradient _ j (freeCriticalPath hDensity hSob h a b
        (freeEnergyState hDensity hSob (-a) u0))‖ ≤ eta := by
  let u := freeEnergyState hDensity hSob (-a) u0
  let loc := freeJoint_coordinates_local_smallness h u a eta heta
  let r : ℝ := Classical.choose loc
  have hr : 0 < r := (Classical.choose_spec loc).1
  have hsmall : ∀ j : Fin 3,
      mixedNorm (volume.restrict (Metric.ball a r)) volume 10 criticalExponent
        (freeJoint (energyGradient j u)) ≤ ENNReal.ofReal eta :=
    (Classical.choose_spec loc).2
  have hsub : Set.Icc a (a + r / 2) ⊆ Metric.ball a r := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]
  refine ⟨a + r / 2, by linarith, shiftedFreeCriticalPath_energy_norm_le
    hDensity hSob h a (a + r / 2) u0, ?_⟩
  intro j
  apply (ENNReal.ofReal_le_ofReal_iff heta.le).mp
  rw [ofReal_norm, freeCriticalPath_gradient_eq_restrict]
  exact (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)).trans (hsmall j)

end HartreeF.ActualDuhamelPath
