import FProfileSpacetimeCutoff
import FProfileEnergyBridge

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileApproximation
open TimeHolder CutoffApproximation SobolevStretch EnergySpace CriticalTimeSobolev

/-- Constant multiplication in time has no spatial derivative term. -/
theorem inDotH1_real_smul {u : Space → ℂ} {U V : Space → Space}
    (h : InDotH1 u U V) (a : ℝ) :
    InDotH1 (fun x => a • u x) (fun x => a • U x) (fun x => a • V x) := by
  refine ⟨h.function_L6.const_smul a, h.real_gradient_L2.const_smul a,
    h.imag_gradient_L2.const_smul a, ?_, ?_⟩
  · have hr := h.real_weak.mul_smooth (χ := fun _ => a) contDiff_const
    simpa only [gradient_fun_const, smul_zero, add_zero, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hr
  · have hi := h.imag_weak.mul_smooth (χ := fun _ => a) contDiff_const
    simpa only [gradient_fun_const, smul_zero, add_zero, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hi

def localizedRealGradient (n : ℕ) (u : ℝ → Space → ℂ)
    (U : ℝ → Space → Space) (t : ℝ) (x : Space) : Space :=
  timeCutoff n t • (cutoff n x • U t x + (u t x).re • gradient (cutoff n) x)

def localizedImagGradient (n : ℕ) (u : ℝ → Space → ℂ)
    (V : ℝ → Space → Space) (t : ℝ) (x : Space) : Space :=
  timeCutoff n t • (cutoff n x • V t x + (u t x).im • gradient (cutoff n) x)

theorem spacetime_cutoff_domain (n : ℕ) {u : ℝ → Space → ℂ}
    {U V : ℝ → Space → Space}
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), InDotH1 (u t) (U t) (V t)) :
    ∀ᵐ t ∂(volume : Measure ℝ), InDotH1 (spacetimeCutoff n u t)
      (localizedRealGradient n u U t) (localizedImagGradient n u V t) :=
  hd.mono fun t ht => inDotH1_real_smul (cutoff_L2_and_dotH1 ht n).2 (timeCutoff n t)

theorem spacetimeCutoffGradient_is_packed (n : ℕ) (u : ℝ → Space → ℂ)
    (U V : ℝ → Space → Space) (t : ℝ) (x : Space) :
    spacetimeCutoffGradient n u (fun s => complexGradient (U s) (V s)) t x =
      complexGradient (localizedRealGradient n u U t) (localizedImagGradient n u V t) x := by
  unfold spacetimeCutoffGradient
  rw [spatialCutoffGradient_is_packed]
  ext j
  apply Complex.ext <;>
    simp [complexGradient, localizedRealGradient, localizedImagGradient, Complex.real_smul,
      mul_add]

theorem spacetimeCutoff_joint_measurable (n : ℕ) {u : ℝ → Space → ℂ}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => spacetimeCutoff n u z.1 z.2)
      (volume.prod volume) :=
  ((timeCutoff_smooth n).continuous.comp continuous_fst).aestronglyMeasurable.smul
    (((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hu)

/-- The genuine compact cutoff has a radius-independent packed homogeneous energy bound. -/
theorem spacetime_cutoff_energy_bound (n : ℕ) (u : ℝ → Space → ℂ)
    (G : ℝ → Space → CGradient)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume ∞ 2 (spacetimeCutoffGradient n u G) ≤
      mixedNorm volume volume ∞ 2 G +
        (cutoffGradientBound : ℝ≥0∞) * mixedNorm volume volume ∞ 6 u :=
  (temporal_cutoff_mixed_le (p := ∞) (q := 2) (by norm_num) (by norm_num) n _
    (spatialCutoffGradient_joint_measurable n hu hG)).trans
      (spatial_cutoff_energy_bound n u G hu hG)

/-- The packed product gradient is compactly supported on the same finite spacetime scale. -/
theorem spacetimeCutoffGradient_compact (n : ℕ) (u : ℝ → Space → ℂ)
    (G : ℝ → Space → CGradient) :
    HasCompactSupport (fun z : ℝ × Space => spacetimeCutoffGradient n u G z.1 z.2) := by
  have hg := WeakCutoffLp.cutoff_gradient_hasCompactSupport (cutoff_compact n)
  apply HasCompactSupport.intro ((timeCutoff_compact n).prod ((cutoff_compact n).union hg))
  intro z hz
  simp only [Set.mem_prod, Set.mem_union] at hz
  by_cases ht : z.1 ∈ tsupport (timeCutoff n)
  · have hx : z.2 ∉ tsupport (cutoff n) := fun hx => hz ⟨ht, Or.inl hx⟩
    have hgx : z.2 ∉ tsupport (gradient (cutoff n)) := fun hx => hz ⟨ht, Or.inr hx⟩
    simp [spacetimeCutoffGradient, spatialCutoffGradient, cutoffCorrection,
      image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hgx, realEmbed_zero]
  · simp [spacetimeCutoffGradient, image_eq_zero_of_notMem_tsupport ht]

theorem mixed_spatial_tail_le {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hqTop : q ≠ ∞) (n : ℕ)
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (fun t => exteriorTail n (f t)) ≤
      mixedNorm volume volume p q f := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => exteriorTail n (f z.1) z.2)
      (volume.prod volume) :=
    hf.indicator (isOpen_lt continuous_const continuous_snd.norm).measurableSet
  apply eLpNorm_mono_enorm_ae (spatial_lp_time_measurable volume volume q hq0 hqTop _ hm)
  filter_upwards [] with t
  exact eLpNorm_indicator_le _
    (isOpen_lt continuous_const continuous_norm).measurableSet.nullMeasurableSet

/-- Uniform critical derivative bound, using S for the cutoff-gradient correction. -/
theorem spacetime_cutoff_W_bound (n : ℕ) (u : ℝ → Space → ℂ)
    (G : ℝ → Space → CGradient)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ)) (spacetimeCutoffGradient n u G) ≤
      mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ)) G +
        (cutoffGradientBound : ℝ≥0∞) * mixedNorm volume volume 10 10 u := by
  have ht := temporal_cutoff_mixed_le (p := 10) (q := ENNReal.ofReal (30 / 13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top n (spatialCutoffGradient n u G)
    (spatialCutoffGradient_joint_measurable n hu hG)
  have ha := mixed_add_le (p := 10) (q := ENNReal.ofReal (30 / 13 : ℝ))
    (by norm_num) (by norm_num) ENNReal.ofReal_ne_top
    (fun t x => cutoff n x • G t x) (cutoffCorrection n u)
    (((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hG)
    (correction_joint_measurable n hu)
  have hc := (correction_mixed_bound n u hu).trans
    (mul_le_mul' le_rfl (mixed_spatial_tail_le (p := 10) (q := 10)
      (by norm_num) (by norm_num) n u hu))
  have hs := spatial_cutoff_mixed_le (p := 10) (q := ENNReal.ofReal (30 / 13 : ℝ))
    (by norm_num) ENNReal.ofReal_ne_top n G hG
  exact (ht.trans ha).trans (add_le_add hs hc)

/-- The compact cutoff contracts the actual S norm. -/
theorem spacetime_cutoff_S_bound (n : ℕ) (u : ℝ → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume 10 10 (spacetimeCutoff n u) ≤ mixedNorm volume volume 10 10 u :=
  (temporal_cutoff_mixed_le (p := 10) (q := 10) (by norm_num) (by norm_num) n
    (fun t x => cutoff n x • u t x)
    (((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hu)).trans
      (spatial_cutoff_mixed_le (p := 10) (q := 10) (by norm_num) (by norm_num) n u hu)

/-- Compact-cutoff energy on actual EnergyState profiles, using the existing joint producer. -/
theorem actual_profile_cutoff_energy {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : AEStronglyMeasurable g volume) (n : ℕ) :
    let r := energyJointFields volume g hg
    mixedNorm volume volume ∞ 2
      (spacetimeCutoffGradient n r.u (fun t => complexGradient (r.U t) (r.V t))) ≤
      (1 + (cutoffGradientBound : ℝ≥0∞) * ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹))) * curveEnergy g := by
  dsimp only
  let r := energyJointFields volume g hg
  have hG := packedGradient_joint_measurable r.joint_U.aestronglyMeasurable
    r.joint_V.aestronglyMeasurable
  have he := spacetime_cutoff_energy_bound n r.u (fun t => complexGradient (r.U t) (r.V t)) r.joint_u.aestronglyMeasurable hG
  have hv := jointFields_value_sobolev_bound hSob g r
  rw [jointFields_energy_eq g r hg] at he
  exact (he.trans (add_le_add le_rfl (mul_le_mul' le_rfl hv))).trans_eq (by ring)

/-- Representative selection preserves every value mixed norm. -/
theorem jointFields_value_mixedNorm (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    (p q : ℝ≥0∞) :
    mixedNorm volume volume p q r.u = mixedNorm volume volume p q (fun t => energyValue (g t)) := by
  apply eLpNorm_congr_ae
  exact r.slice_eq.mono fun _ ht => eLpNorm_congr_ae ht.1

/-- Representative selection preserves every packed-gradient mixed norm. -/
theorem jointFields_packed_mixedNorm (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    (p q : ℝ≥0∞) :
    mixedNorm volume volume p q (fun t => complexGradient (r.U t) (r.V t)) =
      mixedNorm volume volume p q (fun t => complexGradient
        (energyProjectedGradient Complex.reCLM (g t))
        (energyProjectedGradient Complex.imCLM (g t))) := by
  apply eLpNorm_congr_ae
  filter_upwards [r.slice_eq] with t ht
  apply eLpNorm_congr_ae
  filter_upwards [ht.2.1, ht.2.2] with x hU hV
  simp only [complexGradient, hU, hV]

/-- Complete native cutoff stage: same compact value, its actual weak gradients,
convergent S/W errors, and a uniform genuine homogeneous energy bound.
The output is compact and weakly differentiable; smooth mollification is a later stage. -/
theorem actual_profile_compact_cutoff {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : AEStronglyMeasurable g volume)
    (hE : curveEnergy g ≠ ∞)
    (hS : mixedNorm volume volume 10 10 (fun t => energyValue (g t)) ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ))
      (fun t => complexGradient (energyProjectedGradient Complex.reCLM (g t))
        (energyProjectedGradient Complex.imCLM (g t))) ≠ ∞) :
    let r := energyJointFields volume g hg
    (∀ n, HasCompactSupport (fun z : ℝ × Space => spacetimeCutoff n r.u z.1 z.2)) ∧
    (∀ n, ∀ᵐ t ∂(volume : Measure ℝ), InDotH1 (spacetimeCutoff n r.u t)
      (localizedRealGradient n r.u r.U t) (localizedImagGradient n r.u r.V t)) ∧
    Tendsto (fun n => mixedNorm volume volume 10 10
      (fun t x => spacetimeCutoff n r.u t x - r.u t x)) atTop (𝓝 0) ∧
    Tendsto (fun n => mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ))
      (fun t x => spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t x -
        complexGradient (r.U t) (r.V t) x)) atTop (𝓝 0) ∧
    (∀ n, mixedNorm volume volume ∞ 2
      (spacetimeCutoffGradient n r.u (fun t => complexGradient (r.U t) (r.V t))) ≤
      (1 + (cutoffGradientBound : ℝ≥0∞) * ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹))) * curveEnergy g) ∧
    (∀ n, mixedNorm volume volume ∞ 2
      (spacetimeCutoffGradient n r.u (fun t => complexGradient (r.U t) (r.V t))) ≠ ∞) := by
  let r := energyJointFields volume g hg
  have hG := packedGradient_joint_measurable r.joint_U.aestronglyMeasurable
    r.joint_V.aestronglyMeasurable
  have hSr : mixedNorm volume volume 10 10 r.u ≠ ∞ := by
    rwa [jointFields_value_mixedNorm g r]
  have hWr : mixedNorm volume volume 10 (ENNReal.ofReal (30 / 13 : ℝ))
      (fun t => complexGradient (r.U t) (r.V t)) ≠ ∞ := by
    rwa [jointFields_packed_mixedNorm g r]
  have hc := spacetime_cutoff_joint_SW r.u (fun t => complexGradient (r.U t) (r.V t)) r.joint_u.aestronglyMeasurable hG hSr hWr
  have hfinite : (1 + (cutoffGradientBound : ℝ≥0∞) *
      ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹))) * curveEnergy g ≠ ∞ := by finiteness
  exact ⟨fun n => spacetimeCutoff_compact n r.u,
    fun n => spacetime_cutoff_domain n r.inDotH1, hc.1, hc.2,
    fun n => actual_profile_cutoff_energy hSob g hg n,
    fun n => ne_top_of_le_ne_top hfinite (actual_profile_cutoff_energy hSob g hg n)⟩

#print axioms inDotH1_real_smul
#print axioms spacetime_cutoff_domain
#print axioms spacetimeCutoffGradient_is_packed
#print axioms actual_profile_cutoff_energy
#print axioms actual_profile_compact_cutoff
end HartreeF.ProfileApproximation
