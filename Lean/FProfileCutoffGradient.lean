import FProfileMixedTails
import FEnergyGradientNorm

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileApproximation
open TimeHolder CutoffApproximation SobolevStretch

abbrev CGradient := EuclideanSpace ℂ (Fin 3)

def realEmbed (v : Space) : CGradient := WithLp.toLp 2 (fun j => (v j : ℂ))

theorem realEmbed_continuous : Continuous realEmbed := by
  unfold realEmbed
  fun_prop

theorem realEmbed_norm (v : Space) : ‖realEmbed v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, realEmbed]

theorem realEmbed_zero : realEmbed 0 = 0 := by
  ext j
  simp [realEmbed]

/-- The fixed finite L3 gradient bound, obtained from the actual base bump. -/
def cutoffGradientBound : ℝ≥0 :=
  (eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume).toNNReal

theorem cutoffGradientBound_coe : (cutoffGradientBound : ℝ≥0∞) =
    eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume :=
  ENNReal.coe_toNNReal cutoff_gradient_eLpNorm_lt_top.ne

/-- The literal complex vector correction in the product weak gradient. -/
def cutoffCorrection (n : ℕ) (u : ℝ → Space → ℂ) (t : ℝ) (x : Space) : CGradient :=
  u t x • realEmbed (gradient (cutoff n) x)

def spatialCutoffGradient (n : ℕ) (u : ℝ → Space → ℂ)
    (G : ℝ → Space → CGradient) (t : ℝ) (x : Space) : CGradient :=
  cutoff n x • G t x + cutoffCorrection n u t x

theorem correction_joint_measurable (n : ℕ) {u : ℝ → Space → ℂ}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => cutoffCorrection n u z.1 z.2)
      (volume.prod volume) :=
  hu.smul (realEmbed_continuous.comp
    ((WeakCutoffLp.cutoff_gradient_continuous (cutoff_smooth n)).comp continuous_snd)).aestronglyMeasurable

theorem spatialCutoffGradient_joint_measurable (n : ℕ) {u : ℝ → Space → ℂ}
    {G : ℝ → Space → CGradient}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => spatialCutoffGradient n u G z.1 z.2)
      (volume.prod volume) :=
  (((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hG).add
    (correction_joint_measurable n hu)

/-- Homogeneous spatial Holder: no L2 norm of the value occurs. -/
theorem correction_slice_bound {p r : ℝ≥0∞} [ENNReal.HolderTriple p 3 r]
    (hr : 0 < r) (n : ℕ) (u : ℝ → Space → ℂ) (t : ℝ) :
    eLpNorm (cutoffCorrection n u t) r volume ≤
      (cutoffGradientBound : ℝ≥0∞) * eLpNorm (exteriorTail n (u t)) p volume := by
  have hcorr : cutoffCorrection n u t = fun x =>
      exteriorTail n (u t) x • realEmbed (gradient (cutoff n) x) := by
    funext x
    by_cases hx : (n : ℝ) < ‖x‖
    · simp [cutoffCorrection, exteriorTail, Set.indicator, hx]
    · simp [cutoffCorrection, exteriorTail, cutoff_gradient_zero n (le_of_not_gt hx), realEmbed_zero]
  have hnorm : eLpNorm (fun x => realEmbed (gradient (cutoff n) x)) 3 volume =
      (cutoffGradientBound : ℝ≥0∞) := by
    rw [cutoffGradientBound_coe, ← cutoff_gradient_eLpNorm n]
    apply eLpNorm_congr_norm_ae
      (realEmbed_continuous.comp (WeakCutoffLp.cutoff_gradient_continuous
        (cutoff_smooth n))).aestronglyMeasurable
      (WeakCutoffLp.cutoff_gradient_continuous (cutoff_smooth n)).aestronglyMeasurable
    exact ae_of_all _ (fun x => realEmbed_norm _)
  rw [hcorr]
  exact (eLpNorm_smul_le_mul_eLpNorm_of_pos (p := p) (q := 3) (φ := exteriorTail n (u t)) (f := fun x => realEmbed (gradient (cutoff n) x)) hr).trans_eq (by rw [hnorm, mul_comm])

/-- The critical 1/(30/13)=1/10+1/3 Holder identity. -/
theorem critical_correction_holder :
    ENNReal.HolderTriple 10 3 (ENNReal.ofReal (30 / 13 : ℝ)) := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  rw [ENNReal.toReal_add (by simp) (by simp)]
  norm_num

/-- The genuine correction is bounded in W by the vanishing S exterior tail. -/
theorem correction_mixed_bound (n : ℕ) (u : ℝ → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ)) (cutoffCorrection n u) ≤
      (cutoffGradientBound : ℝ≥0∞) *
        mixedNorm volume volume 10 10 (fun t => exteriorTail n (u t)) := by
  let := critical_correction_holder
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (spatial_lp_time_measurable volume volume _ (by norm_num) ENNReal.ofReal_ne_top _
      (correction_joint_measurable n hu))
  exact ae_of_all _ (fun t => correction_slice_bound (by norm_num) n u t)

/-- Actual vector-valued cutoff-gradient correction tends to zero in W. -/
theorem correction_mixed_tendsto_zero (u : ℝ → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hS : mixedNorm volume volume 10 10 u ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ))
      (cutoffCorrection n u)) atTop (𝓝 0) := by
  have htail := mixed_spatial_tail_tendsto_zero (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) u hu hS
  have hb := ENNReal.Tendsto.const_mul htail (a := (cutoffGradientBound : ℝ≥0∞)) (Or.inr (by simp))
  simp only [mul_zero] at hb
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => bot_le) (fun n => correction_mixed_bound n u hu)

/-- Joint convergence of the same spatially cut off value and its product gradient. -/
theorem spatial_cutoff_joint_SW (u : ℝ → Space → ℂ) (G : ℝ → Space → CGradient)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume))
    (hS : mixedNorm volume volume 10 10 u ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ)) G ≠ ∞) :
    Tendsto (fun n => mixedNorm volume volume 10 10
      (fun t x => cutoff n x • u t x - u t x)) atTop (𝓝 0) ∧
    Tendsto (fun n => mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ))
      (fun t x => spatialCutoffGradient n u G t x - G t x)) atTop (𝓝 0) := by
  refine ⟨mixed_spatial_cutoff_tendsto_zero (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) u hu hS, ?_⟩
  have hlin := mixed_spatial_cutoff_tendsto_zero (by norm_num) (by norm_num)
    (by norm_num) ENNReal.ofReal_ne_top G hG hW
  have hcorr := correction_mixed_tendsto_zero u hu hS
  have hsum := hlin.add hcorr
  simp only [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le)
  intro n
  have heq : (fun t x => spatialCutoffGradient n u G t x - G t x) =
      fun t x => (cutoff n x • G t x - G t x) + cutoffCorrection n u t x := by
    funext t x
    unfold spatialCutoffGradient
    abel
  dsimp only
  rw [heq]
  exact mixed_add_le (by norm_num) (by norm_num) ENNReal.ofReal_ne_top _ _
    ((((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hG).sub hG)
    (correction_joint_measurable n hu)

/-- The formal vector above equals the packed two-real weak gradient produced by Leibniz. -/
theorem spatialCutoffGradient_is_packed (n : ℕ) (u : ℝ → Space → ℂ)
    (U V : ℝ → Space → Space) (t : ℝ) (x : Space) :
    spatialCutoffGradient n u (fun s => complexGradient (U s) (V s)) t x =
      complexGradient
        (fun y => cutoff n y • U t y + (u t y).re • gradient (cutoff n) y)
        (fun y => cutoff n y • V t y + (u t y).im • gradient (cutoff n) y) x := by
  ext j
  apply Complex.ext <;>
    simp [spatialCutoffGradient, cutoffCorrection, realEmbed, complexGradient,
      Complex.real_smul]

/-- The slice domain and its literal weak gradients are produced, not assumed. -/
theorem spatial_cutoff_domain (n : ℕ) {u : ℝ → Space → ℂ}
    {U V : ℝ → Space → Space}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), InDotH1 (u t) (U t) (V t)) :
    ∀ᵐ t ∂(volume : Measure ℝ), InDotH1 (fun x => cutoff n x • u t x)
      (fun x => cutoff n x • U t x + (u t x).re • gradient (cutoff n) x)
      (fun x => cutoff n x • V t x + (u t x).im • gradient (cutoff n) x) :=
  hd.mono fun _ ht => (cutoff_L2_and_dotH1 ht n).2

#print axioms correction_slice_bound
#print axioms correction_mixed_bound
#print axioms correction_mixed_tendsto_zero
#print axioms spatial_cutoff_joint_SW
#print axioms spatialCutoffGradient_is_packed
#print axioms spatial_cutoff_domain
end HartreeF.ProfileApproximation
