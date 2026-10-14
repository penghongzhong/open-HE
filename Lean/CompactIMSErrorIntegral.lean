import ActualIMSLocalMass

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation SobolevStretch

/-- Actual IMS error integral controlled by a squared actual exterior L6 tail. -/
theorem ims_error_integral_le_tail {u : Space → ℂ} (hu : MemLp u 6 volume) (n : ℕ) :
    (∫ x, ‖u x‖^2 * ‖gradient (cutoffAngle n) x‖^2) ≤
      imsGradientConstant^2 * (eLpNorm (exteriorTail n u) 6 volume).toReal^2 := by
  have he := function_smul_angle_gradient_L2 (cutoffAngle_valid n) hu.norm
  have hsq := integral_norm_sq_eq_eLpNorm_sq he
  have heq : (∫ x, ‖u x‖^2 * ‖gradient (cutoffAngle n) x‖^2) =
      (eLpNorm (fun x => ‖u x‖ • gradient (cutoffAngle n) x) 2 volume).toReal^2 := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_norm, mul_pow] using hsq
  rw [heq, ← mul_pow]
  apply pow_le_pow_left₀ ENNReal.toReal_nonneg
  exact (angle_correction_real_le_tail hu.norm n).trans
    (mul_le_mul_of_nonneg_left
      (component_tail_real_le hu hu.norm (fun x => by simp) n) imsGradientConstant_nonneg)

/-- A common radius makes the literal IMS error integral small uniformly near a compact family. -/
theorem compact_ims_error_integral_neighborhood {K : Set HomogeneousData}
    (hK : IsCompact (HomogeneousData.lpData '' K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ K, ∀ g : HomogeneousData,
      dist g.lpData f.lpData < δ →
      (∫ x, ‖g.u x‖^2 * ‖gradient (cutoffAngle n) x‖^2) < ε := by
  let C := imsGradientConstant
  have hC : 0 ≤ C := imsGradientConstant_nonneg
  let η := min 1 (ε / (2 * (1 + C)^2))
  have hden : 0 < 2 * (1 + C)^2 := by positivity
  have hη : 0 < η := lt_min (by norm_num) (div_pos hε hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηb : η ≤ ε / (2 * (1 + C)^2) := min_le_right _ _
  have hbudget : C^2 * η^2 < ε := by
    have hh := (le_div_iff₀ hden).mp hηb
    have hηsq : η^2 ≤ η := by nlinarith
    calc
      C^2 * η^2 ≤ (1 + C)^2 * η^2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg η)
      _ ≤ (1 + C)^2 * η := mul_le_mul_of_nonneg_left hηsq (sq_nonneg _)
      _ ≤ ε / 2 := by nlinarith
      _ < ε := by linarith
  obtain ⟨N, hN⟩ := compact_homogeneous_uniform_tails hK hη
  refine ⟨η / 4, by positivity, N, ?_⟩
  intro n hn f hf g hgf
  have ht := (hN n hn f hf g hgf).1
  have hsq : (eLpNorm (exteriorTail n g.u) 6 volume).toReal^2 ≤ η^2 :=
    pow_le_pow_left₀ ENNReal.toReal_nonneg ht.le 2
  exact (ims_error_integral_le_tail g.domain.function_L6 n).trans_lt
    ((mul_le_mul_of_nonneg_left hsq (sq_nonneg C)).trans_lt hbudget)

/-- Actual integral-error uniform convergence, with every n beyond the same N. -/
theorem compact_ims_error_integral {K : Set HomogeneousData}
    (hK : IsCompact (HomogeneousData.lpData '' K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ K,
      (∫ x, ‖f.u x‖^2 * ‖gradient (cutoffAngle n) x‖^2) < ε := by
  obtain ⟨δ, hδ, N, hN⟩ := compact_ims_error_integral_neighborhood hK hε
  exact ⟨N, fun n hn f hf => hN n hn f hf f (by simpa using hδ)⟩

#print axioms ims_error_integral_le_tail
#print axioms compact_ims_error_integral_neighborhood
#print axioms compact_ims_error_integral
end HartreeF.ComplexIMS
