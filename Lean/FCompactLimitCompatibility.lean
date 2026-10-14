import FPositiveTerminalCauchyFamily
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveRealization
open EnergySpace CriticalPathSpace CriticalPathRestriction WaveCauchy
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath

/-- The actual prefix restriction is a contraction on full graph differences. -/
theorem prefixRestrict_difference_norm_le {T S R : ℝ} (hTS : T≤S) (hSR : S≤R)
    (u v : CriticalPath (intervalMeasure T R)) :
    ‖restrictPath le_rfl hTS hSR u-restrictPath le_rfl hTS hSR v‖≤‖u-v‖ := by
  have hb := nested_terminal_difference_bound hTS hSR le_rfl u v
  have hi := restrictPath_self (hTS.trans hSR) v
  exact hb.trans_eq (congrArg (fun w : CriticalPath (intervalMeasure T R) => ‖u-w‖) hi)

/-- Restriction continuity is native graph continuity, not a separate path assumption. -/
theorem prefixRestrict_continuous {T S R : ℝ} (hTS : T≤S) (hSR : S≤R) :
    Continuous (restrictPath le_rfl hTS hSR) := by
  have hL : LipschitzWith 1 (restrictPath le_rfl hTS hSR) := by
    apply LipschitzWith.mk_one
    intro u v
    exact (dist_eq_norm (restrictPath le_rfl hTS hSR u)
      (restrictPath le_rfl hTS hSR v)).le.trans
      ((prefixRestrict_difference_norm_le hTS hSR u v).trans
        (dist_eq_norm u v).symm.le)
  exact hL.continuous

/-- Two fixed compact cutoffs become literally the same terminal time.
Restriction transitivity then gives eventual equality in one graph space. -/
theorem terminalCompactSequence_prefix_eventuallyEq {T S R : ℝ}
    (hTS : T≤S) (hSR : S≤R)
    (U : ∀ r : ℝ, T≤r → CriticalPath (intervalMeasure T r)) :
    (fun n => restrictPath le_rfl hTS hSR (terminalCompactSequence (hTS.trans hSR) U n))
      =ᶠ[atTop] terminalCompactSequence hTS U := by
  let chosen := exists_nat_ge (R-T)
  let N : ℕ := Classical.choose chosen
  have hN : R-T≤(N:ℝ) := Classical.choose_spec chosen
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N:ℝ)≤(n:ℝ) := Nat.cast_le.mpr hn
  have hRn : R≤T+n := by linarith only [hN,hcast]
  have hSn : S≤T+n := hSR.trans hRn
  simp only [terminalCompactSequence,restrictPath_trans]
  let W : Ici S → CriticalPath (intervalMeasure T S) := fun r =>
    restrictPath le_rfl hTS r.property (U r (hTS.trans r.property))
  have hmax : max R (T+n)=max S (T+n) :=
    (max_eq_right hRn).trans (max_eq_right hSn).symm
  exact congrArg W (show (⟨max R (T+n),hSR.trans (le_max_left R (T+n))⟩ : Ici S)=
    ⟨max S (T+n),show S ≤ max S (T+n) from le_max_left S (T+n)⟩ from Subtype.ext hmax)

/-- Compact limit compatibility is produced from the actual common family.
No compatibility field, initial trace equality or PDE uniqueness is assumed. -/
theorem terminalCompactLimits_compatible {T S R : ℝ}
    (hTS : T≤S) (hSR : S≤R)
    (U : ∀ r : ℝ, T≤r → CriticalPath (intervalMeasure T r))
    (u : CriticalPath (intervalMeasure T S)) (v : CriticalPath (intervalMeasure T R))
    (hu : Tendsto (terminalCompactSequence hTS U) atTop (𝓝 u))
    (hv : Tendsto (terminalCompactSequence (hTS.trans hSR) U) atTop (𝓝 v)) :
    restrictPath le_rfl hTS hSR v=u := by
  have hr := ((prefixRestrict_continuous hTS hSR).tendsto v).comp hv
  have he := terminalCompactSequence_prefix_eventuallyEq hTS hSR U
  exact tendsto_nhds_unique hr (hu.congr' he.symm)

end HartreeF.WaveRealization
