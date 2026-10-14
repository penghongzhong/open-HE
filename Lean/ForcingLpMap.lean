import ForcingStrongContinuity

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcingContinuity
open ForcingDomain DotH1Topology

local instance forcingLpExponent_ge_one : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) :=
  ⟨by norm_num⟩

/-- Genuine L6-to-L^(6/5) map, obtained from the literal integral forcing. -/
def forcingLp {α c : ℝ} (hH : OrdinaryHLS α c)
    (u : Lp ℂ 6 (volume : Measure Space)) :
    Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure Space) :=
  (forcing_memLp hH (Lp.memLp u)).toLp (forcing α c u)

/-- The output distance uses the literal forcing evaluated on actual representatives. -/
theorem forcingLp_distance {α c : ℝ} (hH : OrdinaryHLS α c)
    (u v : Lp ℂ 6 (volume : Measure Space)) :
    dist (forcingLp hH u) (forcingLp hH v) =
      (eLpNorm (forcing α c u-forcing α c v)
        (ENNReal.ofReal (6/5 : ℝ)) volume).toReal :=
  toLp_distance (forcing_memLp hH (Lp.memLp u)) (forcing_memLp hH (Lp.memLp v))

theorem inputLp_distance (u v : Lp ℂ 6 (volume : Measure Space)) :
    dist u v = (eLpNorm (fun x => u x-v x) 6 volume).toReal := by
  simpa only [Lp.toLp_coeFn] using toLp_distance (Lp.memLp u) (Lp.memLp v)

/-- Every bounded L6 ball has a finite Lipschitz constant. -/
theorem forcingLp_lipschitzOn_norm_ball {α c : ℝ} (hH : OrdinaryHLS α c)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ≥0, LipschitzOnWith L (forcingLp hH) {u | ‖u‖ ≤ R} := by
  obtain ⟨L,hL,hbound⟩ := forcing_difference_bound_on_ball hH R hR
  refine ⟨⟨L,hL⟩,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro u hu v hv
  rw [forcingLp_distance,inputLp_distance]
  exact hbound u v (Lp.memLp u) (Lp.memLp v) hu hv

/-- Local Lipschitz continuity in an explicit open neighborhood of every L6 point. -/
theorem forcingLp_locally_lipschitz {α c : ℝ} (hH : OrdinaryHLS α c)
    (v : Lp ℂ 6 (volume : Measure Space)) :
    ∃ L : ℝ≥0, LipschitzOnWith L (forcingLp hH) (Metric.ball v 1) := by
  obtain ⟨L,hL⟩ := forcingLp_lipschitzOn_norm_ball hH (‖v‖+1) (by positivity)
  refine ⟨L,hL.mono ?_⟩
  intro u hu
  change ‖u‖ ≤ ‖v‖+1
  have hd : ‖u-v‖ ≤ 1 := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hu).le
  calc
    ‖u‖ = ‖u-v+v‖ := by rw [sub_add_cancel]
    _ ≤ ‖u-v‖+‖v‖ := norm_add_le _ _
    _ ≤ 1+‖v‖ := add_le_add hd le_rfl
    _ = _ := by ring

/-- The actual Hartree nonlinearity is a continuous map L6→L^(6/5). -/
theorem forcingLp_continuous {α c : ℝ} (hH : OrdinaryHLS α c) :
    Continuous (forcingLp hH) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply tendsto_iff_dist_tendsto_zero.mpr
  rw [show (fun u => dist (forcingLp hH u) (forcingLp hH v)) =
      (fun u : Lp ℂ 6 (volume : Measure Space) => (eLpNorm (forcing α c u-forcing α c v)
        (ENNReal.ofReal (6/5 : ℝ)) volume).toReal) by funext u; exact forcingLp_distance hH u v]
  apply strong_forcing_tendsto hH (fun u => (Lp.memLp u)) (Lp.memLp v)
  simpa only [inputLp_distance, id_eq, Pi.sub_def] using
    (tendsto_iff_dist_tendsto_zero.mp (tendsto_id : Tendsto id (𝓝 v) (𝓝 v)))

#print axioms forcingLp_distance
#print axioms inputLp_distance
#print axioms forcingLp_lipschitzOn_norm_ball
#print axioms forcingLp_locally_lipschitz
#print axioms forcingLp_continuous
end HartreeF.ForcingContinuity
