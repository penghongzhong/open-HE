import DominatedL2Convergence

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ModulusGradient

theorem strong_l2_zero_add {E : Type*} [NormedAddCommGroup E]
    {fn gn : ℕ → Space → E}
    (hf : Tendsto (fun n => eLpNorm (fn n) 2 volume) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (gn n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fn n + gn n) 2 volume) atTop (𝓝 0) := by
  have h := hf.add hg
  simp only [zero_add] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun _ => bot_le) (fun _ => eLpNorm_add_le (by norm_num))

theorem strong_l2_zero_of_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {fn : ℕ → Space → E} {gn : ℕ → Space → F} {B : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (fn n) volume)
    (hbound : ∀ n, ∀ᵐ x ∂volume, ‖fn n x‖ ≤ B * ‖gn n x‖)
    (hg : Tendsto (fun n => eLpNorm (gn n) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fn n) 2 volume) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul (a := ‖B‖ₑ) hg (Or.inr enorm_ne_top)
  simp only [mul_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
  intro n
  calc
    eLpNorm (fn n) 2 volume ≤ eLpNorm (B • gn n) 2 volume := by
      apply eLpNorm_mono_ae (hf n)
      filter_upwards [hbound n] with x hx
      exact hx.trans (by simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg (gn n x)))
    _ = ‖B‖ₑ * eLpNorm (gn n) 2 volume := eLpNorm_const_smul B (gn n) 2 volume

/-- Multiplication by bounded varying scalar coefficients is continuous when
the coefficients converge a.e. and the actual vector fields converge in L2. -/
theorem bounded_varying_coefficient_smul_strong_l2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {cn : ℕ → Space → ℝ} {c : Space → ℝ}
    {Gn : ℕ → Space → E} {G : Space → E} {B : ℝ}
    (hcn : ∀ n, AEStronglyMeasurable (cn n) volume)
    (hc : AEStronglyMeasurable c volume)
    (hGn : ∀ n, MemLp (Gn n) 2 volume) (hG : MemLp G 2 volume)
    (hboundn : ∀ n, ∀ᵐ x ∂volume, ‖cn n x‖ ≤ B)
    (hbound : ∀ᵐ x ∂volume, ‖c x‖ ≤ B)
    (hclim : ∀ᵐ x ∂volume, Tendsto (fun n => cn n x) atTop (𝓝 (c x)))
    (hGlim : Tendsto (fun n => eLpNorm (Gn n - G) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => cn n x • Gn n x - c x • G x) 2 volume)
      atTop (𝓝 0) := by
  have hfirst : Tendsto (fun n => eLpNorm
      (fun x => cn n x • (Gn n x - G x)) 2 volume) atTop (𝓝 0) := by
    apply strong_l2_zero_of_norm_le
      (fun n => (hcn n).smul ((hGn n).sub hG).aestronglyMeasurable) (B := B)
      (gn := fun n => Gn n - G)
    · intro n
      filter_upwards [hboundn n] with x hx
      exact (norm_smul (cn n x) (Gn n x - G x)).le.trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    · exact hGlim
  have hsecond := bounded_coefficient_smul_strong_l2 hcn hc hG
    (B := B + B) (fun n => by
      filter_upwards [hboundn n, hbound] with x hn hx
      exact (norm_sub_le _ _).trans (add_le_add hn hx)) hclim
  have hsum := strong_l2_zero_add hfirst hsecond
  convert hsum using 1
  funext n
  congr 1
  funext x
  simp only [Pi.add_apply, smul_sub, sub_smul]
  abel

#print axioms strong_l2_zero_add
#print axioms strong_l2_zero_of_norm_le
#print axioms bounded_varying_coefficient_smul_strong_l2
end HartreeF.ModulusGradient
