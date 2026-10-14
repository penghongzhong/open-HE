import FNegativeInitialCauchyFamily
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.IncomingWaveRealization
open EnergySpace CriticalPathSpace CriticalPathRestriction WaveInitialCauchy
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath

/-- Actual suffix restriction contracts full graph differences. -/
theorem suffixRestrict_difference_norm_le {T S R : ℝ} (hST : S≤T) (hRS : R≤S)
    (u v : CriticalPath (intervalMeasure R T)) :
    ‖restrictPath hRS hST le_rfl u-restrictPath hRS hST le_rfl v‖≤‖u-v‖ := by
  have hb := nested_initial_difference_bound hST hRS le_rfl u v
  have hi := restrictPath_self (hRS.trans hST) v
  exact hb.trans_eq (congrArg (fun w : CriticalPath (intervalMeasure R T) => ‖u-w‖) hi)

/-- Genuine graph restriction is continuous. -/
theorem suffixRestrict_continuous {T S R : ℝ} (hST : S≤T) (hRS : R≤S) :
    Continuous (restrictPath hRS hST le_rfl) := by
  have hL : LipschitzWith 1 (restrictPath hRS hST le_rfl) := by
    apply LipschitzWith.mk_one
    intro u v
    exact (dist_eq_norm (restrictPath hRS hST le_rfl u)
      (restrictPath hRS hST le_rfl v)).le.trans
      ((suffixRestrict_difference_norm_le hST hRS u v).trans
        (dist_eq_norm u v).symm.le)
  exact hL.continuous

/-- Two compact cutoffs eventually have the identical initial time T-n.
Restriction transitivity then gives literal equality in the common graph. -/
theorem initialCompactSequence_suffix_eventuallyEq {T S R : ℝ}
    (hST : S≤T) (hRS : R≤S)
    (U : ∀ r : ℝ, r≤T → CriticalPath (intervalMeasure r T)) :
    (fun n => restrictPath hRS hST le_rfl (initialCompactSequence (hRS.trans hST) U n))
      =ᶠ[atTop] initialCompactSequence hST U := by
  let chosen := exists_nat_ge (T-R)
  let N : ℕ := Classical.choose chosen
  have hN : T-R≤(N:ℝ) := Classical.choose_spec chosen
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N:ℝ)≤(n:ℝ) := Nat.cast_le.mpr hn
  have hnR : T-n≤R := by linarith only [hN,hcast]
  have hnS : T-n≤S := hnR.trans hRS
  simp only [initialCompactSequence,restrictPath_trans]
  let W : Iic S → CriticalPath (intervalMeasure S T) := fun r =>
    restrictPath r.property hST le_rfl (U r (r.property.trans hST))
  have hmin : min R (T-n)=min S (T-n) :=
    (min_eq_right hnR).trans (min_eq_right hnS).symm
  exact congrArg W (show (⟨min R (T-n),(min_le_left R (T-n)).trans hRS⟩ : Iic S)=
    ⟨min S (T-n),show min S (T-n) ≤ S from min_le_left S (T-n)⟩ from Subtype.ext hmin)

/-- Compatibility is a consequence of the common actual family and strong
limits, rather than an assumed compatibility or trace field. -/
theorem initialCompactLimits_compatible {T S R : ℝ}
    (hST : S≤T) (hRS : R≤S)
    (U : ∀ r : ℝ, r≤T → CriticalPath (intervalMeasure r T))
    (u : CriticalPath (intervalMeasure S T)) (v : CriticalPath (intervalMeasure R T))
    (hu : Tendsto (initialCompactSequence hST U) atTop (𝓝 u))
    (hv : Tendsto (initialCompactSequence (hRS.trans hST) U) atTop (𝓝 v)) :
    restrictPath hRS hST le_rfl v=u := by
  have hr := ((suffixRestrict_continuous hST hRS).tendsto v).comp hv
  have he := initialCompactSequence_suffix_eventuallyEq hST hRS U
  exact tendsto_nhds_unique hr (hu.congr' he.symm)

end HartreeF.IncomingWaveRealization
