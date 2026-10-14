import CompactLocalMass

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace Metric
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation SobolevStretch

/-- The quotient representative has exactly the local mass of the supplied actual L6 field. -/
theorem localBall_toLp_mass_eq {u : Space → ℂ} (hu : MemLp u 6 volume) (n : ℕ) :
    (∫ x in localBall n, ‖(hu.toLp u) x‖^2) = ∫ x in localBall n, ‖u x‖^2 := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hu.coeFn_toLp] with x hx
  rw [hx]

/-- Exact conventional finite-volume exponent in the local L2 bound. -/
theorem localBall_mass_upper_volume {u : Space → ℂ} (hu : MemLp u 6 volume) (n : ℕ) :
    (∫ x in localBall n, ‖u x‖^2) ≤
      (volume (localBall n)).toReal ^ (2 / 3 : ℝ) * (eLpNorm u 6 volume).toReal^2 := by
  have hh := localBall_mass_upper hu n
  have he : (localL2Constant n)^2 = (volume (localBall n)).toReal ^ (2 / 3 : ℝ) := by
    unfold localL2Constant
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
  rwa [he] at hh

/-- Any sufficiently large actual cosine core preserves all mass in a fixed inner ball. -/
theorem local_mass_le_core_mass {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) {N n : ℕ} (hNn : N ≤ n) :
    (∫ x in localBall N, ‖u x‖^2) ≤ ∫ x, ‖core (cutoffAngle n) u x‖^2 := by
  have he : (∫ x in localBall N, ‖u x‖^2) =
      ∫ x in localBall N, ‖core (cutoffAngle n) u x‖^2 := by
    apply setIntegral_congr_fun (localBall_measurable N)
    intro x hx
    have hxN : ‖x‖ ≤ (N : ℝ) := by simpa only [localBall, mem_closedBall, dist_zero_right] using hx
    have hh : (N : ℝ) ≤ n := by exact_mod_cast hNn
    change ‖u x‖^2 = ‖core (cutoffAngle n) u x‖^2
    rw [core_cutoffAngle_eq_self_inside n u (by linarith : ‖x‖ ≤ (n : ℝ) + 1)]
  rw [he]
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall (fun x => sq_nonneg ‖core (cutoffAngle n) u x‖))
    ((core_L2 (cutoffAngle_valid n) hu).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))

/-- Actual nonzero complex fields in a compact homogeneous family have a common positive core mass. -/
theorem compact_actual_core_mass_lower {K : Set HomogeneousData}
    (hK : IsCompact (HomogeneousData.lpData '' K))
    (hnonzero : ∀ f ∈ K, ¬ (f.u =ᵐ[volume] 0)) :
    ∃ N : ℕ, ∃ m > 0, ∀ n ≥ N, ∀ f ∈ K,
      m ≤ ∫ x, ‖core (cutoffAngle n) f.u x‖^2 := by
  have hL6 := hK.image continuous_fst
  have hz : (0 : Lp ℂ 6 (volume : Measure Space)) ∉ Prod.fst '' (HomogeneousData.lpData '' K) := by
    rintro ⟨v, ⟨f, hf, rfl⟩, hv⟩
    have hzero : f.domain.function_L6.toLp f.u = 0 := hv
    have hae := Lp.eq_zero_iff_ae_eq_zero.mp hzero
    exact hnonzero f hf (f.domain.function_L6.coeFn_toLp.symm.trans hae)
  obtain ⟨N, m, hm, hmass⟩ := compact_nonzero_local_mass_lower hL6 hz
  refine ⟨N, m, hm, ?_⟩
  intro n hn f hf
  have hh := hmass f.lpData.1 (mem_image_of_mem _ (mem_image_of_mem _ hf))
  have hh' : m ≤ ∫ x in localBall N, ‖f.u x‖^2 := by
    simpa only [HomogeneousData.lpData, localBall_toLp_mass_eq] using hh
  exact hh'.trans (local_mass_le_core_mass f.domain hn)

#print axioms localBall_toLp_mass_eq
#print axioms localBall_mass_upper_volume
#print axioms local_mass_le_core_mass
#print axioms compact_actual_core_mass_lower
end HartreeF.ComplexIMS
