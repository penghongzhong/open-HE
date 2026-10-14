import FNegativeInitialApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.WaveInitialCauchy
open EnergySpace CriticalPathSpace CriticalSourceBounds ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest ActualStrichartz CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath restrictPath

/-- Genuine early graph error controls each actual energy value, including endpoints. -/
theorem initial_early_error_at (hDensity : OrdinaryH1Density) {K Ch T A R t epsilon : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hAT : A ≤ T) (hRA : R ≤ A) (hRt : R ≤ t) (htA : t ≤ A)
    (phi : EnergyState) (u : CriticalPath (intervalMeasure R T))
    (herr : ‖restrictPath le_rfl hRA hAT u -
      freeCriticalPath hDensity hSob hfree R A phi‖ ≤ epsilon) :
    ‖energyPath _ u ⟨t,hRt,htA.trans hAT⟩ - freeEnergyState hDensity hSob t phi‖ ≤ epsilon := by
  let w := restrictPath le_rfl hRA hAT u
  let f := freeCriticalPath hDensity hSob hfree R A phi
  let s : Icc R A := ⟨t,hRt,htA⟩
  have he : energyPath (intervalMeasure R A) (w-f) s =
      energyPath _ u ⟨t,hRt,htA.trans hAT⟩ - freeEnergyState hDensity hSob t phi :=
    (energyPath_sub_apply _ w f s).trans
      (congrArg₂ (fun x y : EnergyState => x-y)
        (restrictPath_energy le_rfl hRA hAT u s)
        (freeCriticalPath_energy hDensity hSob hfree R A phi s))
  exact (congrArg norm he).symm.le.trans
    ((energyPath_value_norm_le _ (w-f) s).trans herr)

/-- A comparison on the common larger interval controls the same smaller compact
paths, using genuine restriction transitivity and linearity. -/
theorem nested_initial_difference_bound {T S R1 R2 : ℝ}
    (hST : S ≤ T) (hR1S : R1 ≤ S) (hR2R1 : R2 ≤ R1)
    (u : CriticalPath (intervalMeasure R1 T)) (v : CriticalPath (intervalMeasure R2 T)) :
    ‖restrictPath hR1S hST le_rfl u - restrictPath (hR2R1.trans hR1S) hST le_rfl v‖ ≤
      ‖u - restrictPath hR2R1 (hR1S.trans hST) le_rfl v‖ := by
  let w := restrictPath hR2R1 (hR1S.trans hST) le_rfl v
  have hc := restrictPath_trans hR2R1 (hR1S.trans hST) le_rfl hR1S hST le_rfl v
  have hl : restrictPath hR1S hST le_rfl (u-w) =
      restrictPath hR1S hST le_rfl u-restrictPath hR1S hST le_rfl w := by
    apply energyPath_injective
    apply ContinuousMap.ext
    intro t
    exact (restrictPath_energy hR1S hST le_rfl (u-w) t).trans
      ((energyPath_sub_apply (intervalMeasure R1 T) u w (intervalInclusion hR1S le_rfl t)).trans
        ((congrArg₂ (fun x y : EnergyState => x-y)
          (restrictPath_energy hR1S hST le_rfl u t).symm
          (restrictPath_energy hR1S hST le_rfl w t).symm).trans
            (energyPath_sub_apply (intervalMeasure S T)
              (restrictPath hR1S hST le_rfl u) (restrictPath hR1S hST le_rfl w) t).symm))
  have he : restrictPath hR1S hST le_rfl (u-w) =
      restrictPath hR1S hST le_rfl u - restrictPath (hR2R1.trans hR1S) hST le_rfl v :=
    hl.trans (congrArg (fun z : CriticalPath (intervalMeasure S T) =>
      restrictPath hR1S hST le_rfl u-z) hc)
  exact (congrArg norm he).symm.le.trans (restrictPath_norm_le hR1S hST le_rfl (u-w))

/-- Every term lives in the SAME compact CriticalPath space on [S,T]. -/
def initialCompactSequence {T S : ℝ} (hST : S ≤ T)
    (U : ∀ R : ℝ, R ≤ T → CriticalPath (intervalMeasure R T))
    (n : ℕ) : CriticalPath (intervalMeasure S T) :=
  restrictPath (min_le_left S (T-n)) hST le_rfl
    (U (min S (T-n)) ((min_le_left _ _).trans hST))

end HartreeF.WaveInitialCauchy
