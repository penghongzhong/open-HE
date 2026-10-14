import LocalL2Restriction

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation

/-- If the actual local L2 restriction vanishes, the L6 field equals its exterior tail. -/
theorem exterior_eq_of_localBallLp_eq_zero (n : ℕ) (f : Lp ℂ 6 (volume : Measure Space))
    (hf : localBallLp n f = 0) :
    eLpNorm (exteriorTail n f) 6 volume = eLpNorm (f : Space → ℂ) 6 volume := by
  have hz := Lp.eq_zero_iff_ae_eq_zero.mp hf
  have hc := (localBall_memLp_two (Lp.memLp f) n).coeFn_toLp
  have hi : (localBall n).indicator (f : Space → ℂ) =ᵐ[volume] 0 := hc.symm.trans hz
  apply eLpNorm_congr_ae
  filter_upwards [hi] with x hx
  unfold exteriorTail
  by_cases hxn : (n : ℝ) < ‖x‖
  · simp [Set.indicator, hxn]
  · have hin : x ∈ localBall n := by
      simpa only [localBall, mem_closedBall, dist_zero_right] using le_of_not_gt hxn
    have hfx : f x = 0 := by simpa only [Set.indicator_of_mem hin, Pi.zero_apply] using hx
    simp [Set.indicator, hxn, hfx]

/-- A compact nonzero L6 family has a single ball on which every actual L2 restriction is nonzero. -/
theorem compact_nonzero_exists_localBall {K : Set (Lp ℂ 6 (volume : Measure Space))}
    (hK : IsCompact K) (hzero : (0 : Lp ℂ 6 (volume : Measure Space)) ∉ K) :
    ∃ N : ℕ, ∀ f ∈ K, 0 < ‖localBallLp N f‖ := by
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le' continuous_norm.continuousOn
    (a := 0) (fun f hf => norm_pos_iff.mpr (by intro hz; exact hzero (hz ▸ hf)))
  obtain ⟨N, hN⟩ := compact_exteriorLp_uniform (by norm_num : (6 : ℝ≥0∞) ≠ ∞) hK hm
  refine ⟨N, ?_⟩
  intro f hf
  apply norm_pos_iff.mpr
  intro hz
  have ht := hN N le_rfl f hf
  rw [exteriorLp_norm, exterior_eq_of_localBallLp_eq_zero N f hz, ← Lp.norm_def] at ht
  exact (not_lt_of_ge (hmin f hf)) ht

/-- A fixed-ball positive local mass bound is uniform over any compact nonzero L6 family. -/
theorem compact_nonzero_local_mass_lower {K : Set (Lp ℂ 6 (volume : Measure Space))}
    (hK : IsCompact K) (hzero : (0 : Lp ℂ 6 (volume : Measure Space)) ∉ K) :
    ∃ N : ℕ, ∃ m > 0, ∀ f ∈ K, m ≤ ∫ x in localBall N, ‖f x‖^2 := by
  obtain ⟨N, hN⟩ := compact_nonzero_exists_localBall hK hzero
  have hc : Continuous (fun f : Lp ℂ 6 (volume : Measure Space) => ‖localBallLp N f‖) :=
    continuous_norm.comp (localBallLp_lipschitz N).continuous
  obtain ⟨b, hb, hbK⟩ := hK.exists_forall_le' hc.continuousOn hN
  refine ⟨N, b^2, sq_pos_of_pos hb, ?_⟩
  intro f hf
  rw [localBallLp_mass]
  exact pow_le_pow_left₀ hb.le (hbK f hf) 2

/-- The positive local mass bound persists in a fixed L6 neighborhood of the compact family. -/
theorem compact_nonzero_local_mass_neighborhood {K : Set (Lp ℂ 6 (volume : Measure Space))}
    (hK : IsCompact K) (hzero : (0 : Lp ℂ 6 (volume : Measure Space)) ∉ K) :
    ∃ N : ℕ, ∃ m > 0, ∃ δ > 0, ∀ f ∈ K, ∀ g : Lp ℂ 6 (volume : Measure Space),
      dist g f < δ → m ≤ ∫ x in localBall N, ‖g x‖^2 := by
  obtain ⟨N, hN⟩ := compact_nonzero_exists_localBall hK hzero
  have hc : Continuous (fun f : Lp ℂ 6 (volume : Measure Space) => ‖localBallLp N f‖) :=
    continuous_norm.comp (localBallLp_lipschitz N).continuous
  obtain ⟨b, hb, hbK⟩ := hK.exists_forall_le' hc.continuousOn hN
  let δ := b / (2 * (1 + localL2Constant N))
  have hC := localL2Constant_nonneg N
  have hδ : 0 < δ := div_pos hb (by linarith)
  refine ⟨N, (b / 2)^2, sq_pos_of_pos (by linarith), δ, hδ, ?_⟩
  intro f hf g hgf
  have hden : 0 < 2 * (1 + localL2Constant N) := by linarith
  have hdist : (1 + localL2Constant N) * dist g f < b / 2 := by
    have hh := (lt_div_iff₀ hden).mp hgf
    nlinarith
  have hcontr := (localBallLp_lipschitz N).dist_le_mul f g
  rw [Real.coe_toNNReal _ hC, dist_comm f g] at hcontr
  have hnorm : ‖localBallLp N f‖ ≤ ‖localBallLp N g‖ + dist (localBallLp N f) (localBallLp N g) := by
    simpa only [dist_eq_norm, norm_sub_rev] using norm_le_norm_add_norm_sub (localBallLp N g) (localBallLp N f)
  have hlow : b / 2 ≤ ‖localBallLp N g‖ := by
    have hbf := hbK f hf
    have hd := dist_nonneg (x := g) (y := f)
    nlinarith
  rw [localBallLp_mass]
  exact pow_le_pow_left₀ (by linarith) hlow 2

#print axioms exterior_eq_of_localBallLp_eq_zero
#print axioms compact_nonzero_exists_localBall
#print axioms compact_nonzero_local_mass_lower
#print axioms compact_nonzero_local_mass_neighborhood
end HartreeF.ComplexIMS
