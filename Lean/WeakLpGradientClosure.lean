import ActualPairingContinuity
import WeakGradientClosure

/-! Genuine weak-gradient closure with distinct function and gradient Lp exponents.
This is an ordinary limit mechanism, not a Hartree chain-rule assumption. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.WeakLpClosure
open SobolevStretch StationaryPairing

theorem strong_linear_map_tendsto
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {p : ℝ≥0∞} {un : ℕ → Space → E} {u : Space → E}
    (hun : ∀ n, MemLp (un n) p volume) (hu : MemLp u p volume)
    (ht : Tendsto (fun n => eLpNorm (un n-u) p volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => L (un n x)-L (u x)) p volume) atTop (𝓝 0) := by
  have hbound (n : ℕ) : eLpNorm (fun x => L (un n x)-L (u x)) p volume ≤
      ENNReal.ofReal ‖L‖*eLpNorm (un n-u) p volume := by
    calc
      _ ≤ eLpNorm (fun x => ‖L‖ • ‖un n x-u x‖) p volume := by
        apply eLpNorm_mono_ae
          ((L.comp_memLp' (hun n)).sub (L.comp_memLp' hu)).aestronglyMeasurable
        filter_upwards [] with x
        simpa only [Pi.sub_apply, Function.comp_def, ← L.map_sub, smul_eq_mul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))] using
          L.le_opNorm (un n x-u x)
      _ = _ := by
        change eLpNorm (‖L‖ • (fun x => ‖(un n-u) x‖)) p volume = _
        rw [eLpNorm_const_smul]
        rw [Real.enorm_eq_ofReal (norm_nonneg _)]
        congr 1
        exact eLpNorm_norm _ ((hun n).sub hu).aestronglyMeasurable
  have hb := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖L‖) ht
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) hbound

theorem weak_test_domains_of_mixed_Lp {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) {u : Space → ℝ} {G : Space → Space}
    (hu : MemLp u p volume) (hG : MemLp G q volume)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (v : Space) :
    Integrable (fun x => u x*fderiv ℝ φ x v) volume ∧
    Integrable (fun x => ⟪G x,v⟫*φ x) volume :=
  weak_test_integrable (hu.locallyIntegrable hp) (hG.locallyIntegrable hq) hφ hc v

theorem hasWeakGradient_of_mixed_Lp_limit {p q p' q' : ℝ≥0∞}
    [ENNReal.HolderTriple p' p 1] [ENNReal.HolderTriple q' q 1]
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    {u : Space → ℝ} {G : Space → Space}
    {un : ℕ → Space → ℝ} {Gn : ℕ → Space → Space}
    (hu : MemLp u p volume) (hG : MemLp G q volume)
    (hun : ∀ n, MemLp (un n) p volume) (hGn : ∀ n, MemLp (Gn n) q volume)
    (hw : ∀ n, HasWeakGradient (un n) (Gn n))
    (hut : Tendsto (fun n => eLpNorm (un n-u) p volume) atTop (𝓝 0))
    (hGt : Tendsto (fun n => eLpNorm (Gn n-G) q volume) atTop (𝓝 0)) :
    HasWeakGradient u G := by
  refine ⟨hu.locallyIntegrable hp,hG.locallyIntegrable hq,?_⟩
  intro v φ hφ hc
  have hd : MemLp (fun x => fderiv ℝ φ x v) p' volume :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have htest : MemLp φ q' volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hscalar := (innerSL ℝ v).comp_memLp' hG
  have hscalarn (n : ℕ) := (innerSL ℝ v).comp_memLp' (hGn n)
  have hscalarT := strong_linear_map_tendsto (innerSL ℝ v) hGn hG hGt
  have hl := integral_mul_tendsto_of_eLpNorm hd hu hun hut
  have hr := integral_mul_tendsto_of_eLpNorm htest hscalar hscalarn hscalarT
  have hl' : Tendsto (fun n => ∫ x, un n x*fderiv ℝ φ x v) atTop
      (𝓝 (∫ x, u x*fderiv ℝ φ x v)) := by
    simpa only [mul_comm] using hl
  have hr' : Tendsto (fun n => -(∫ x, ⟪Gn n x,v⟫*φ x)) atTop
      (𝓝 (-(∫ x, ⟪G x,v⟫*φ x))) := by
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm v, mul_comm] using hr.neg
  apply tendsto_nhds_unique hl'
  convert hr' using 1
  funext n
  exact (hw n).integration_by_parts v φ hφ hc

#print axioms strong_linear_map_tendsto
#print axioms weak_test_domains_of_mixed_Lp
#print axioms hasWeakGradient_of_mixed_Lp_limit
end HartreeF.WeakLpClosure
