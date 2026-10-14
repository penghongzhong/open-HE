import FLocalFreePathCaps
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

/-- The backward free path attains its arbitrary energy datum at the terminal time. -/
theorem backwardFreeCriticalPath_terminal (hDensity : OrdinaryH1Density) {K C a b : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (hab : a ≤ b) (ub : EnergyState) :
    energyPath _ (freeCriticalPath hDensity hSob h a b
      (freeEnergyState hDensity hSob (-b) ub)) ⟨b, hab, le_rfl⟩ = ub := by
  rw [freeCriticalPath_energy]
  exact freeEnergyState_inverse hDensity hSob b ub

set_option maxHeartbeats 200000 in
set_option diagnostics true in
/-- Every datum has a positive backward compact interval on which all three
actual free critical coordinates are arbitrarily small. Only finiteness from
the numerical homogeneous Strichartz estimate enters time localization. -/
theorem exists_backwardFreeCriticalPath_small (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (b : ℝ) (u0 : EnergyState) (eta : ℝ) (heta : 0 < eta) :
    ∃ a : ℝ, a < b ∧
      ‖energyPath _ (freeCriticalPath hDensity hSob h a b
        (freeEnergyState hDensity hSob (-b) u0))‖ ≤
        (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) * ‖u0‖ ∧
      ∀ j : Fin 3, ‖criticalGradient _ j (freeCriticalPath hDensity hSob h a b
        (freeEnergyState hDensity hSob (-b) u0))‖ ≤ eta := by
  let u := freeEnergyState hDensity hSob (-b) u0
  let loc := freeJoint_coordinates_local_smallness h u b eta heta
  let r : ℝ := Classical.choose loc
  have hr : 0 < r := (Classical.choose_spec loc).1
  have hsmall : ∀ j : Fin 3,
      mixedNorm (volume.restrict (Metric.ball b r)) volume 10 criticalExponent
        (freeJoint (energyGradient j u)) ≤ ENNReal.ofReal eta :=
    (Classical.choose_spec loc).2
  have hsub : Set.Icc (b - r / 2) b ⊆ Metric.ball b r := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
    linarith [ht.1]
  refine ⟨b - r / 2, by linarith, ?_, ?_⟩
  · apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    rw [freeCriticalPath_energy, ← freeEnergyState_add_time]
    exact freeEnergyState_norm_bound hDensity hSob ((t : ℝ) + -b) u0
  · intro j
    apply (ENNReal.ofReal_le_ofReal_iff heta.le).mp
    rw [ofReal_norm, freeCriticalPath_gradient_eq_restrict]
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)).trans (hsmall j)

end HartreeF.ActualDuhamelPath
