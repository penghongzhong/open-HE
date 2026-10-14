import FPositiveTerminalApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.WaveCauchy
open EnergySpace CriticalPathSpace CriticalSourceBounds ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest ActualStrichartz CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath restrictPath

/-- Genuine graph error controls each actual energy value, including endpoints. -/
theorem terminal_late_error_at (hDensity : OrdinaryH1Density) {K Ch T A R t epsilon : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hTA : T ≤ A) (hAR : A ≤ R) (hAt : A ≤ t) (htR : t ≤ R)
    (phi : EnergyState) (u : CriticalPath (intervalMeasure T R))
    (herr : ‖restrictPath hTA hAR le_rfl u -
      freeCriticalPath hDensity hSob hfree A R phi‖ ≤ epsilon) :
    ‖energyPath _ u ⟨t,hTA.trans hAt,htR⟩ - freeEnergyState hDensity hSob t phi‖ ≤ epsilon := by
  let w := restrictPath hTA hAR le_rfl u
  let f := freeCriticalPath hDensity hSob hfree A R phi
  let s : Icc A R := ⟨t,hAt,htR⟩
  have he : energyPath (intervalMeasure A R) (w-f) s =
      energyPath _ u ⟨t,hTA.trans hAt,htR⟩ - freeEnergyState hDensity hSob t phi :=
    (energyPath_sub_apply _ w f s).trans
      (congrArg₂ (fun x y : EnergyState => x-y)
        (restrictPath_energy hTA hAR le_rfl u s)
        (freeCriticalPath_energy hDensity hSob hfree A R phi s))
  exact (congrArg norm he).symm.le.trans
    ((energyPath_value_norm_le _ (w-f) s).trans herr)

/-- Comparing on a common larger interval controls the same smaller compact
paths. Restriction transitivity and linearity are used literally. -/
theorem nested_terminal_difference_bound {T S R1 R2 : ℝ}
    (hTS : T ≤ S) (hSR1 : S ≤ R1) (hR1R2 : R1 ≤ R2)
    (u : CriticalPath (intervalMeasure T R1)) (v : CriticalPath (intervalMeasure T R2)) :
    ‖restrictPath le_rfl hTS hSR1 u - restrictPath le_rfl hTS (hSR1.trans hR1R2) v‖ ≤
      ‖u - restrictPath le_rfl (hTS.trans hSR1) hR1R2 v‖ := by
  let w := restrictPath le_rfl (hTS.trans hSR1) hR1R2 v
  have hc := restrictPath_trans le_rfl (hTS.trans hSR1) hR1R2 le_rfl hTS hSR1 v
  have hl : restrictPath le_rfl hTS hSR1 (u-w) =
      restrictPath le_rfl hTS hSR1 u-restrictPath le_rfl hTS hSR1 w := by
    apply energyPath_injective
    apply ContinuousMap.ext
    intro t
    exact (restrictPath_energy le_rfl hTS hSR1 (u-w) t).trans
      ((energyPath_sub_apply (intervalMeasure T R1) u w (intervalInclusion le_rfl hSR1 t)).trans
        ((congrArg₂ (fun x y : EnergyState => x-y)
          (restrictPath_energy le_rfl hTS hSR1 u t).symm
          (restrictPath_energy le_rfl hTS hSR1 w t).symm).trans
            (energyPath_sub_apply (intervalMeasure T S)
              (restrictPath le_rfl hTS hSR1 u) (restrictPath le_rfl hTS hSR1 w) t).symm))
  have he : restrictPath le_rfl hTS hSR1 (u-w) =
      restrictPath le_rfl hTS hSR1 u - restrictPath le_rfl hTS (hSR1.trans hR1R2) v :=
    hl.trans (congrArg (fun z : CriticalPath (intervalMeasure T S) =>
      restrictPath le_rfl hTS hSR1 u-z) hc)
  exact (congrArg norm he).symm.le.trans (restrictPath_norm_le le_rfl hTS hSR1 (u-w))

/-- All terms live in the SAME compact CriticalPath space. -/
def terminalCompactSequence {T S : ℝ} (hTS : T ≤ S)
    (U : ∀ R : ℝ, T ≤ R → CriticalPath (intervalMeasure T R))
    (n : ℕ) : CriticalPath (intervalMeasure T S) :=
  restrictPath le_rfl hTS (le_max_left S (T+n))
    (U (max S (T+n)) (hTS.trans (le_max_left _ _)))

end HartreeF.WaveCauchy
