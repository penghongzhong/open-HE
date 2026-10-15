import DirectionalKineticPositive

/-! R8.4 Lemma 7.4, equation (46), with the actual sixth integral and
the actual weak-gradient directional kinetic integral. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory
namespace HartreeF.Paper121Directional
open SobolevStretch DirectionalStretch

theorem directional_sixth_bound {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm)
    (hne : ¬ u =ᵐ[volume] 0) {omega : Space} (homega : ‖omega‖ = 1) :
    (∫ x, ‖u x‖ ^ 6) ≤
      8 * K * (kinetic GRe GIm) ^ 2 * directionalKinetic omega GRe GIm := by
  let A := kinetic GRe GIm
  let d := directionalKinetic omega GRe GIm
  have hd : 0 < d := directionalKinetic_pos hSob hu hne homega
  have hm := sixth_mass_pos hu.function_L6 hne
  have hA : 0 < A := by
    have hbound := hSob.bound hu
    have hnonneg := kinetic_nonneg GRe GIm
    by_contra hn
    have hz : A = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    change (∫ x, ‖u x‖ ^ 6) ≤ K * A ^ 3 at hbound
    rw [hz] at hbound
    norm_num only [zero_pow, mul_zero] at hbound
    exact (not_lt_of_ge hbound) hm
  let l := Real.sqrt (A / d)
  have hl : 0 < l := Real.sqrt_pos.mpr (div_pos hA hd)
  have hl2 : l ^ 2 = A / d := Real.sq_sqrt (div_pos hA hd).le
  have hkin : kinetic (stretchedGradient omega l GRe)
      (stretchedGradient omega l GIm) = 2 * A - d := by
    rw [kinetic_stretch hu homega hl, hl2]
    change A - d + (A / d) * d = 2 * A - d
    rw [div_mul_cancel₀ _ hd.ne']
    ring
  have hkin0 : 0 ≤ 2 * A - d := by
    rw [← hkin]
    exact kinetic_nonneg _ _
  have hcube : (2 * A - d) ^ 3 ≤ (2 * A) ^ 3 :=
    pow_le_pow_left₀ hkin0 (by linarith) 3
  have hbound := hSob.bound (hu.stretch homega hl)
  rw [sixth_mass_stretch homega hl u, hl2, hkin] at hbound
  have hupper : (A / d) * (∫ x, ‖u x‖ ^ 6) ≤ 8 * K * A ^ 3 := by
    calc
      _ ≤ K * (2 * A - d) ^ 3 := hbound
      _ ≤ K * (2 * A) ^ 3 := mul_le_mul_of_nonneg_left hcube hSob.nonneg
      _ = _ := by ring
  apply (mul_le_mul_iff_right₀ hA).mp
  calc
    A * (∫ x, ‖u x‖ ^ 6) = ((A / d) * (∫ x, ‖u x‖ ^ 6)) * d := by
      field_simp [hd.ne']
    _ ≤ (8 * K * A ^ 3) * d := mul_le_mul_of_nonneg_right hupper hd.le
    _ = A * (8 * K * A ^ 2 * d) := by ring

end HartreeF.Paper121Directional
