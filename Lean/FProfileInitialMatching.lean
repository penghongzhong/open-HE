import FCountableActualNonlinearProfiles
import FR2FamilyTailAlgebra

/-! Initial matching for the original finite depth and original sequence.
The critical affine map is used in its actual EnergyState graph norm, followed
by the fixed sqrt(3) comparison with the pure-gradient norm. UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileInitialMatching
open EnergySpace SobolevStretch StationarySelfTest ProfileEnergy CriticalAffine
  R2Global R2Frames R2FamilyTail Retarded ActualStrichartz EndpointOutput
  ForcingDomain MaximalTrajectory CountableNonlinearProfiles

/-- Exact reconstruction at zero. Every summand uses the original normalized
matching time and the original physical affine map. -/
theorem augmented_initial_difference (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) (J n : ℕ) :
    augmentedCurve hDensity hSob P u g J n 0 - u n =
      ∑ j ∈ Finset.range J,
        criticalAffineState (P.scale j n) (P.scale_pos j n) (P.center j n)
          (g j (P.time j n) -
            freeEnergyState hDensity hSob (P.time j n) (P.profile j)) := by
  rw [augmentedCurve_cancellation]
  simp only [Pi.add_apply, Finset.sum_apply, freeCurve, freeEnergyState_zero_time]
  rw [add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro j _
  simp only [physicalCorrection, Pi.sub_apply, nonlinearFrame, stateFrame_time,
    zero_div, add_zero, freeCurve, freeEnergyState_zero_time, profileAtom,
    linearProfileFrame_apply, map_sub]

/-- The estimate is for the graph norm actually preserved by criticalAffineState.
No symmetry assertion about an unproved pure-gradient operation is used. -/
theorem initial_graph_norm_le (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) (J n : ℕ) :
    ‖u n - augmentedCurve hDensity hSob P u g J n 0‖ ≤
      ∑ j ∈ Finset.range J, ‖g j (P.time j n) -
        freeEnergyState hDensity hSob (P.time j n) (P.profile j)‖ := by
  rw [norm_sub_rev, augmented_initial_difference]
  calc
    _ ≤ ∑ j ∈ Finset.range J,
      ‖criticalAffineState (P.scale j n) (P.scale_pos j n) (P.center j n)
        (g j (P.time j n) -
          freeEnergyState hDensity hSob (P.time j n) (P.profile j))‖ := norm_sum_le _ _
    _ = _ := Finset.sum_congr rfl (fun j _ =>
      (criticalAffineState (P.scale j n) (P.scale_pos j n) (P.center j n)).norm_map _)

/-- Fixed finite J matching on the SAME actual canonical family. The marked
original solution that will be approximated is at (0,u n), independently of J. -/
theorem actual_initial_matching (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre α c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS α c)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (T : ℕ → ℝ)
    (f : ℕ → EnergyState)
    (hmatch : ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hH P T f)
    (J : ℕ) :
    let g := fun j =>
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH (T j) (f j)).state
    Tendsto (fun n => pureGradientNorm
      (u n - augmentedCurve hDensity hSob P u g J n 0)) atTop (𝓝 0) := by
  dsimp only
  let g := fun j =>
    (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH (T j) (f j)).state
  have hm := (finite_profile_control hDensity hSob h0 hfree hret hefree heret hH
    hmatch (Finset.range J)).2
  have hlimit : Tendsto (fun n => Real.sqrt 3 *
      ∑ j ∈ Finset.range J, ‖g j (P.time j n) -
        freeEnergyState hDensity hSob (P.time j n) (P.profile j)‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using hm.const_mul (Real.sqrt 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimit
  · intro n
    exact pureGradientNorm_nonneg _
  · intro n
    exact (pureGradient_le_sqrt_three_energyState _).trans
      (mul_le_mul_of_nonneg_left (initial_graph_norm_le hDensity hSob P u g J n)
        (Real.sqrt_nonneg _))

/-- The eventual threshold may depend on J; neither a uniform J rate nor an
initial equality is asserted. -/
theorem actual_initial_matching_eventually (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre α c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS α c)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (T : ℕ → ℝ)
    (f : ℕ → EnergyState)
    (hmatch : ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hH P T f)
    (J : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let g := fun j =>
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH (T j) (f j)).state
    ∃ N : ℕ, ∀ n ≥ N, pureGradientNorm
      (u n - augmentedCurve hDensity hSob P u g J n 0) ≤ ε := by
  have hm := actual_initial_matching hDensity hSob h0 hfree hret hefree heret hH
    P u T f hmatch J
  exact eventually_atTop.mp ((hm.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le))

end HartreeF.ProfileInitialMatching
