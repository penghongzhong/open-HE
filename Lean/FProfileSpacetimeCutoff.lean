import FProfileCutoffGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileApproximation
open TimeHolder CutoffApproximation SobolevStretch

def timeBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
def timeCutoff (n : ℕ) (t : ℝ) : ℝ := timeBump (cutoffScale n * t)

theorem timeCutoff_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (timeCutoff n) :=
  timeBump.contDiff.comp (contDiff_const.mul contDiff_id)

theorem timeCutoff_compact (n : ℕ) : HasCompactSupport (timeCutoff n) := by
  let e : ℝ ≃ₜ ℝ := Homeomorph.smul (Units.mk0 (cutoffScale n) (cutoffScale_pos n).ne')
  exact timeBump.hasCompactSupport.comp_homeomorph e

theorem timeCutoff_nonneg (n : ℕ) (t : ℝ) : 0 ≤ timeCutoff n t := timeBump.nonneg
theorem timeCutoff_le_one (n : ℕ) (t : ℝ) : timeCutoff n t ≤ 1 := timeBump.le_one

theorem timeCutoff_eventually_one (t : ℝ) : ∀ᶠ n : ℕ in atTop, timeCutoff n t = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  filter_upwards [eventually_ge_atTop N] with n hn
  apply timeBump.one_of_mem_closedBall
  simp only [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_mul,
    abs_of_pos (cutoffScale_pos n)]
  change ((n : ℝ) + 1)⁻¹ * |t| ≤ 1
  apply (inv_mul_le_iff₀ (by positivity)).2
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem timeCutoff_norm_le_one (n : ℕ) (t : ℝ) : ‖timeCutoff n t‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (timeCutoff_nonneg n t)]
  exact timeCutoff_le_one n t

theorem timeCutoff_error_norm_le_one (n : ℕ) (t : ℝ) : ‖timeCutoff n t - 1‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [timeCutoff_nonneg n t, timeCutoff_le_one n t]

theorem temporal_cutoff_mixed_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hqTop : q ≠ ∞) (n : ℕ)
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (fun t x => timeCutoff n t • f t x) ≤
      mixedNorm volume volume p q f := by
  apply mixed_mono hq0 hqTop
    (((timeCutoff_smooth n).continuous.comp continuous_fst).aestronglyMeasurable.smul hf)
  intro t x
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (timeCutoff_norm_le_one n t) (norm_nonneg _)).trans_eq
    (one_mul _)

theorem temporal_cutoff_tendsto_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (hq0 : q ≠ 0) (hqTop : q ≠ ∞)
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfin : mixedNorm volume volume p q f ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume p q
      (fun t x => timeCutoff n t • f t x - f t x)) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z : ℝ × Space => timeCutoff n z.1 • f z.1 z.2 - f z.1 z.2)
      (volume.prod volume) :=
    (((timeCutoff_smooth n).continuous.comp continuous_fst).aestronglyMeasurable.smul hf).sub hf
  apply ennreal_eLpNorm_dominated_zero volume hp0 hpTop
    (fun n => spatial_lp_time_measurable volume volume q hq0 hqTop _ (hm n)) hfin
  · intro n
    filter_upwards [hf.prodMk_left] with t ht
    apply eLpNorm_mono (((aestronglyMeasurable_const.smul ht)).sub ht)
    intro x
    change ‖timeCutoff n t • f t x - f t x‖ ≤ ‖f t x‖
    rw [show timeCutoff n t • f t x - f t x = (timeCutoff n t - 1) • f t x by
      rw [sub_smul, one_smul], norm_smul]
    exact (mul_le_mul_of_nonneg_right (timeCutoff_error_norm_le_one n t)
      (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards [] with t
    apply tendsto_const_nhds.congr'
    filter_upwards [timeCutoff_eventually_one t] with n hn
    simp [hn]

/-- The product cutoff uses the same index in space and time. -/
def spacetimeCutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → Space → E) (t : ℝ) (x : Space) : E :=
  timeCutoff n t • (cutoff n x • f t x)

def spacetimeCutoffGradient (n : ℕ) (u : ℝ → Space → ℂ)
    (G : ℝ → Space → CGradient) (t : ℝ) (x : Space) : CGradient :=
  timeCutoff n t • spatialCutoffGradient n u G t x

/-- Compact support holds for the actual rough cutoff field, with no value L2 premise. -/
theorem spacetimeCutoff_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (f : ℝ → Space → E) :
    HasCompactSupport (fun z : ℝ × Space => spacetimeCutoff n f z.1 z.2) := by
  apply HasCompactSupport.intro ((timeCutoff_compact n).prod (cutoff_compact n))
  intro z hz
  simp only [Set.mem_prod] at hz
  by_cases ht : z.1 ∈ tsupport (timeCutoff n)
  · have hx : z.2 ∉ tsupport (cutoff n) := fun hx => hz ⟨ht, hx⟩
    simp [spacetimeCutoff, image_eq_zero_of_notMem_tsupport hx]
  · simp [spacetimeCutoff, image_eq_zero_of_notMem_tsupport ht]

attribute [local irreducible] timeCutoff cutoff cutoffCorrection spatialCutoffGradient

/-- Diagonal spatial-temporal cutoff convergence in any finite mixed exponent pair. -/
theorem spacetime_cutoff_tendsto_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞) (hq : 1 ≤ q) (hqTop : q ≠ ∞)
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hfin : mixedNorm volume volume p q f ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume p q
      (fun t x => spacetimeCutoff n f t x - f t x)) atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le hp)
  have hq0 : q ≠ 0 := ne_of_gt ((by norm_num : (0 : ℝ≥0∞) < 1).trans_le hq)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z : ℝ × Space => spacetimeCutoff n f z.1 z.2 - f z.1 z.2)
      (volume.prod volume) :=
    ((((timeCutoff_smooth n).continuous.comp continuous_fst).aestronglyMeasurable.smul
      (((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hf)).sub hf)
  apply ennreal_eLpNorm_dominated_zero volume hp0 hpTop
    (fun n => spatial_lp_time_measurable volume volume q hq0 hqTop _ (hm n)) hfin
  · intro n
    filter_upwards [(hm n).prodMk_left] with t ht
    apply eLpNorm_mono ht
    intro x
    change ‖timeCutoff n t • (cutoff n x • f t x) - f t x‖ ≤ ‖f t x‖
    rw [smul_smul, show (timeCutoff n t * cutoff n x) • f t x - f t x =
      (timeCutoff n t * cutoff n x - 1) • f t x by rw [sub_smul, one_smul], norm_smul]
    have hb : ‖timeCutoff n t * cutoff n x - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      have hnon := mul_nonneg (timeCutoff_nonneg n t) (cutoff_nonneg n x)
      have hone : timeCutoff n t * cutoff n x ≤ 1 :=
        (mul_le_mul_of_nonneg_right (timeCutoff_le_one n t) (cutoff_nonneg n x)).trans
          (by simpa only [one_mul] using cutoff_le_one n x)
      constructor <;> linarith
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards [finite_mixedNorm_ae_slice_memLp volume volume p q hp0 hpTop f hfin]
      with t ht
    apply (cutoff_eLpNorm_tendsto_zero ht hq0 hqTop).congr'
    filter_upwards [timeCutoff_eventually_one t] with n hn
    simp only [spacetimeCutoff, hn, one_smul]

/-- One compact spacetime cutoff approximates both the value and its packed product gradient. -/
theorem spacetime_cutoff_joint_SW (u : ℝ → Space → ℂ) (G : ℝ → Space → CGradient)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume))
    (hS : mixedNorm volume volume 10 10 u ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ)) G ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume 10 10
      (fun t x => spacetimeCutoff n u t x - u t x)) atTop (𝓝 0) ∧
    Tendsto (fun n => mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ))
      (fun t x => spacetimeCutoffGradient n u G t x - G t x)) atTop (𝓝 0) := by
  refine ⟨spacetime_cutoff_tendsto_zero (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) u hu hS, ?_⟩
  have hsum := (spatial_cutoff_joint_SW u G hu hG hS hW).2.add
    (temporal_cutoff_tendsto_zero (by norm_num) (by norm_num) (by norm_num)
      ENNReal.ofReal_ne_top G hG hW)
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le)
  intro n
  dsimp only
  have hs := (spatialCutoffGradient_joint_measurable n hu hG).sub hG
  have heq : (fun t x => spacetimeCutoffGradient n u G t x - G t x) =
      fun t x => timeCutoff n t • (spatialCutoffGradient n u G t x - G t x) +
        (timeCutoff n t • G t x - G t x) := by
    funext t x
    unfold spacetimeCutoffGradient
    rw [smul_sub]
    abel
  rw [heq]
  have hA := ((timeCutoff_smooth n).continuous.comp continuous_fst).aestronglyMeasurable.smul hs
  have hB := (((timeCutoff_smooth n).continuous.comp continuous_fst).aestronglyMeasurable.smul hG).sub hG
  have htri := mixed_add_le (p := 10) (q := ENNReal.ofReal (30 / 13 : ℝ))
    (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
    (fun t x => timeCutoff n t • (spatialCutoffGradient n u G t x - G t x))
    (fun t x => timeCutoff n t • G t x - G t x) hA hB
  have hcontract := temporal_cutoff_mixed_le (p := 10) (q := ENNReal.ofReal (30 / 13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top n
    (fun t x => spatialCutoffGradient n u G t x - G t x) hs
  exact htri.trans (add_le_add hcontract le_rfl)

#print axioms spacetimeCutoff_compact
#print axioms temporal_cutoff_tendsto_zero
#print axioms spacetime_cutoff_tendsto_zero
#print axioms spacetime_cutoff_joint_SW
end HartreeF.ProfileApproximation
