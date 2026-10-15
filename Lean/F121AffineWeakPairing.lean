import FCriticalAffineL2Continuity

/-! Actual L2 affine pairings: center-uniform Schwartz estimates and two density steps. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Paper121WeakPairing
open EnergySpace CriticalAffine

private theorem affine_schwartz_ae {a : ℝ} (ha : 0 < a) (b : Space) (φ : Test) :
    (gradientAffineL2 ha b (φ.toLp 2 volume) : Space → ℂ) =ᵐ[volume]
      gradientPullback a b φ := by
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae (φ.coeFn_toLp 2 volume)
  filter_upwards [gradientAffineL2_ae ha b (φ.toLp 2 volume), hi] with x hx hi
  simpa only [gradientPullback, hi] using hx

theorem schwartz_pairing {a : ℝ} (ha : 0 < a) (b : Space) (φ ψ : Test) :
    inner ℝ (gradientAffineL2 ha b (φ.toLp 2 volume)) (ψ.toLp 2 volume) =
      ∫ x, inner ℝ (gradientPullback a b φ x) (ψ x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [affine_schwartz_ae ha b φ, ψ.coeFn_toLp 2 volume] with x hx hy
  rw [hx, hy]

theorem schwartz_pairing_small_bound {a : ℝ} (ha : 0 < a) (b : Space) (φ ψ : Test) :
    ‖inner ℝ (gradientAffineL2 ha b (φ.toLp 2 volume)) (ψ.toLp 2 volume)‖ ≤
      (a * Real.sqrt a) * (SchwartzMap.seminorm ℝ 0 0 φ * ∫ x, ‖ψ x‖) := by
  rw [schwartz_pairing]
  have hc : 0 ≤ a * Real.sqrt a := mul_nonneg ha.le (Real.sqrt_nonneg _)
  calc
    _ ≤ ∫ x, ((a * Real.sqrt a) * SchwartzMap.seminorm ℝ 0 0 φ) * ‖ψ x‖ := by
      apply norm_integral_le_of_norm_le (ψ.integrable.norm.const_mul _)
      exact Eventually.of_forall fun x => by
        calc
          ‖inner ℝ (gradientPullback a b φ x) (ψ x)‖ ≤
              ‖gradientPullback a b φ x‖ * ‖ψ x‖ := norm_inner_le_norm _ _
          _ = ((a * Real.sqrt a) * ‖φ (affine a b x)‖) * ‖ψ x‖ := by
            rw [gradientPullback, norm_smul, Real.norm_of_nonneg hc]
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ φ _) hc)
            (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; ring

theorem schwartz_pairing_large_bound {a : ℝ} (ha : 0 < a) (b : Space) (φ ψ : Test) :
    ‖inner ℝ (gradientAffineL2 ha b (φ.toLp 2 volume)) (ψ.toLp 2 volume)‖ ≤
      (a⁻¹ * Real.sqrt a⁻¹) * ((∫ x, ‖φ x‖) * SchwartzMap.seminorm ℝ 0 0 ψ) := by
  rw [schwartz_pairing]
  have hc : 0 ≤ a * Real.sqrt a := mul_nonneg ha.le (Real.sqrt_nonneg _)
  have hφ : Integrable (fun x => ‖gradientPullback a b φ x‖) volume :=
    ((affine_integrable ha.ne' b φ.integrable).smul (a * Real.sqrt a)).norm
  have hcoeff : (a * Real.sqrt a) * (a ^ 3)⁻¹ = a⁻¹ * Real.sqrt a⁻¹ := by
    have hs : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ha)
    have hsq : (a * Real.sqrt a) ^ 2 = a ^ 3 := by
      rw [mul_pow, Real.sq_sqrt ha.le]
      ring
    calc
      _ = (a * Real.sqrt a) * ((a * Real.sqrt a) * (a * Real.sqrt a))⁻¹ := by
        rw [← hsq, pow_two]
      _ = (a * Real.sqrt a)⁻¹ := by
        rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (mul_ne_zero ha.ne' hs), one_mul]
      _ = _ := by rw [mul_inv_rev, Real.sqrt_inv]; ring
  calc
    _ ≤ ∫ x, ‖gradientPullback a b φ x‖ * SchwartzMap.seminorm ℝ 0 0 ψ := by
      apply norm_integral_le_of_norm_le (hφ.mul_const _)
      exact Eventually.of_forall fun x =>
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
          (SchwartzMap.norm_le_seminorm ℝ ψ x) (norm_nonneg _))
    _ = _ := by
      simp only [gradientPullback, norm_smul, Real.norm_of_nonneg hc]
      rw [integral_mul_const, integral_const_mul, affine_integral ha b (fun x => ‖φ x‖),
        smul_eq_mul]
      rw [← mul_assoc, hcoeff]
      ring

/-- The two approximation steps use isometry and Cauchy--Schwarz uniformly
over all affine parameters. No scalar L2 hypothesis on an energy state occurs. -/
theorem weak_pairing_of_schwartz
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    (h : ∀ φ ψ : Test, Tendsto (fun n =>
      inner ℝ (gradientAffineL2 (ha n) (b n) (φ.toLp 2 volume)) (ψ.toLp 2 volume))
        atTop (𝓝 0)) (G H : L2) :
    Tendsto (fun n => inner ℝ (gradientAffineL2 (ha n) (b n) G) H) atTop (𝓝 0) := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := Space) (p := 2)
    (μ := (volume : Measure Space)) (by norm_num)
  have hfixed (ψ : Test) (G : L2) : Tendsto (fun n =>
      inner ℝ (gradientAffineL2 (ha n) (b n) G) (ψ.toLp 2 volume)) atTop (𝓝 0) := by
    let H : L2 := ψ.toLp 2 volume
    have hlip (n : ℕ) : LipschitzWith ‖H‖₊
        (fun G : L2 => inner ℝ (gradientAffineL2 (ha n) (b n) G) H) := by
      apply LipschitzWith.of_dist_le_mul
      intro G₁ G₂
      simp only [dist_eq_norm]
      change ‖inner ℝ (gradientAffineL2 (ha n) (b n) G₁) H -
        inner ℝ (gradientAffineL2 (ha n) (b n) G₂) H‖ ≤ ‖H‖ * ‖G₁ - G₂‖
      rw [← inner_sub_left, ← map_sub]
      calc
        _ ≤ ‖gradientAffineL2 (ha n) (b n) (G₁ - G₂)‖ * ‖H‖ := norm_inner_le_norm _ _
        _ = _ := by rw [LinearIsometry.norm_map]; ring
    have heq := (LipschitzWith.uniformEquicontinuous _ ‖H‖₊ hlip).equicontinuous
    have hclosed : IsClosed {G : L2 | Tendsto (fun n =>
        inner ℝ (gradientAffineL2 (ha n) (b n) G) H) atTop (𝓝 0)} :=
      heq.isClosed_setOfPred_tendsto continuous_const
    exact hd.induction_on G hclosed (fun φ => h φ ψ)
  have hlip (n : ℕ) : LipschitzWith ‖G‖₊
      (fun H : L2 => inner ℝ (gradientAffineL2 (ha n) (b n) G) H) := by
    apply LipschitzWith.of_dist_le_mul
    intro H₁ H₂
    simp only [dist_eq_norm]
    change ‖inner ℝ (gradientAffineL2 (ha n) (b n) G) H₁ -
      inner ℝ (gradientAffineL2 (ha n) (b n) G) H₂‖ ≤ ‖G‖ * ‖H₁ - H₂‖
    rw [← inner_sub_right]
    simpa only [LinearIsometry.norm_map] using
      (norm_inner_le_norm (gradientAffineL2 (ha n) (b n) G) (H₁ - H₂))
  have heq := (LipschitzWith.uniformEquicontinuous _ ‖G‖₊ hlip).equicontinuous
  have hclosed : IsClosed {H : L2 | Tendsto (fun n =>
      inner ℝ (gradientAffineL2 (ha n) (b n) G) H) atTop (𝓝 0)} :=
    heq.isClosed_setOfPred_tendsto continuous_const
  exact hd.induction_on H hclosed (fun ψ => hfixed ψ G)

end HartreeF.Paper121WeakPairing
