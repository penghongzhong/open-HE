import FCriticalPathJointSources

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.CriticalSourceBounds
open EnergySpace CriticalPathSpace CriticalTimeSobolev TimeHolder SobolevStretch
open StationarySelfTest ForcingDomain GradientMajorants WeakHartreeProduct CriticalJointSources
attribute [local irreducible] jointFields energySubmodule criticalPathSubmodule


theorem energyValue_norm_le (z : EnergyState) : ‖energyValue z‖ ≤ ‖z‖ := by
  rw [energyValue_apply]
  exact energyState_value_norm_le z

theorem energyPath_sub_apply {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    (μ : Measure T) (z w : CriticalPath μ) (t : T) :
    energyPath μ (z-w) t = energyPath μ z t - energyPath μ w t :=
  congrArg (fun f : C(T, EnergyState) => f t) ((energyPath μ).map_sub z w)

theorem enorm_sum_three_const (A : ℝ≥0∞) : (∑ _j : Fin 3, A) = 3*A := by simp

attribute [local irreducible] energyPath criticalGradient energyValue energyGradient

theorem energyValue_sub_ae (z w : EnergyState) :
    (energyValue (z-w) : Space → ℂ) =ᵐ[volume]
      (fun x => energyValue z x - energyValue w x) := by
  have he := (energyValue.map_sub z w)
  have hr : (energyValue (z-w) : Space → ℂ) =ᵐ[volume] (energyValue z - energyValue w : L6) :=
    Eventually.of_forall (fun x => congrArg (fun F : L6 => F x) he)
  exact hr.trans (Lp.coeFn_sub _ _)

theorem mixedNorm_congr_slices {T : Type*} [MeasurableSpace T] (μ : Measure T)
    {E : Type*} [NormedAddCommGroup E]
    (p q : ℝ≥0∞) {f g : T → Space → E}
    (h : ∀ᵐ t ∂μ, f t =ᵐ[volume] g t) :
    mixedNorm μ volume p q f = mixedNorm μ volume p q g := by
  exact eLpNorm_congr_ae (h.mono fun _ ht => eLpNorm_congr_ae ht)

theorem projectedGradient_sub_ae (L : ℂ →L[ℝ] ℝ) (z w : EnergyState) :
    energyProjectedGradient L (z-w) =ᵐ[volume]
      (fun x => energyProjectedGradient L z x - energyProjectedGradient L w x) := by
  have h (j : Fin 3) : (energyGradient j (z-w) : Space → ℂ) =ᵐ[volume]
      (fun x => energyGradient j z x - energyGradient j w x) := by
    have he := (energyGradient j).map_sub z w
    have hr : (energyGradient j (z-w) : Space → ℂ) =ᵐ[volume] (energyGradient j z - energyGradient j w : L2) :=
      Eventually.of_forall (fun x => congrArg (fun F : L2 => F x) he)
    exact hr.trans (Lp.coeFn_sub _ _)
  filter_upwards [eventually_all.mpr h] with x hx
  unfold energyProjectedGradient
  simp_rw [hx]
  simp only [map_sub, sub_smul, Finset.sum_sub_distrib]

theorem joint_sub_slices {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z w : CriticalPath μ) :
    ∀ᵐ t ∂μ,
      (jointFields μ (z-w)).u t =ᵐ[volume] ((jointFields μ z).u t - (jointFields μ w).u t) ∧
      (jointFields μ (z-w)).U t =ᵐ[volume] ((jointFields μ z).U t - (jointFields μ w).U t) ∧
      (jointFields μ (z-w)).V t =ᵐ[volume] ((jointFields μ z).V t - (jointFields μ w).V t) := by
  filter_upwards [(jointFields μ (z-w)).slice_eq, (jointFields μ z).slice_eq,
    (jointFields μ w).slice_eq] with t hd hz hw
  have he := energyPath_sub_apply μ z w t
  have hv : (energyValue (energyPath μ (z-w) t) : Space → ℂ) =ᵐ[volume]
      (fun x => energyValue (energyPath μ z t) x - energyValue (energyPath μ w t) x) := by
    have hr : (energyValue (energyPath μ (z-w) t) : Space → ℂ) =ᵐ[volume]
        (energyValue (energyPath μ z t - energyPath μ w t) : Space → ℂ) :=
      Eventually.of_forall (fun x => congrArg (fun F : EnergyState => energyValue F x) he)
    exact hr.trans (energyValue_sub_ae _ _)
  have hG (L : ℂ →L[ℝ] ℝ) : energyProjectedGradient L (energyPath μ (z-w) t) =ᵐ[volume]
      (fun x => energyProjectedGradient L (energyPath μ z t) x - energyProjectedGradient L (energyPath μ w t) x) := by
    have hr : energyProjectedGradient L (energyPath μ (z-w) t) =ᵐ[volume]
        energyProjectedGradient L (energyPath μ z t - energyPath μ w t) :=
      Eventually.of_forall (fun x => congrArg (fun F : EnergyState => energyProjectedGradient L F x) he)
    exact hr.trans (projectedGradient_sub_ae L _ _)
  refine ⟨?_, ?_, ?_⟩
  · exact (hd.1.trans hv).trans (hz.1.sub hw.1).symm
  · exact (hd.2.1.trans (hG Complex.reCLM)).trans (hz.2.1.sub hw.2.1).symm
  · exact (hd.2.2.trans (hG Complex.imCLM)).trans (hz.2.2.sub hw.2.2).symm


set_option maxHeartbeats 1000000 in
theorem joint_value_energy_projection_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z : CriticalPath μ) :
    mixedNorm μ volume ∞ 6 (jointFields μ z).u ≤ ENNReal.ofReal ‖energyPath μ z‖ := by
  have hm := spatial_lp_time_measurable μ volume 6 (by norm_num) (by norm_num)
    (jointFields μ z).u (jointFields μ z).joint_u.aestronglyMeasurable
  have hb : ∀ᵐ t ∂μ, ‖eLpNorm ((jointFields μ z).u t) 6 volume‖ₑ ≤ ENNReal.ofReal ‖energyPath μ z‖ := by
    filter_upwards [(jointFields μ z).slice_eq] with t ht
    have he : eLpNorm ((jointFields μ z).u t) 6 volume =
        ‖energyValue (energyPath μ z t)‖ₑ :=
      (eLpNorm_congr_ae ht.1).trans (Lp.enorm_def (energyValue (energyPath μ z t))).symm
    calc
      _ = ‖energyValue (energyPath μ z t)‖ₑ := by simpa only [enorm_eq_self] using he
      _ = ENNReal.ofReal ‖energyValue (energyPath μ z t)‖ := (ofReal_norm _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        ((energyValue_norm_le (energyPath μ z t)).trans ((energyPath μ z).norm_coe_le_norm t))
  exact (eLpNorm_exponent_top hm).le.trans (eLpNormEssSup_le_of_ae_enorm_bound hb)


theorem joint_value_energy_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z : CriticalPath μ) :
    mixedNorm μ volume ∞ 6 (jointFields μ z).u ≤ ENNReal.ofReal ‖z‖ :=
  (joint_value_energy_projection_bound μ z).trans
    (ENNReal.ofReal_le_ofReal (energyPath_norm_le μ z))

def pathGradientSize {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z : CriticalPath μ) : ℝ≥0∞ :=
  mixedNorm μ volume 10 criticalExponent (jointFields μ z).U +
  mixedNorm μ volume 10 criticalExponent (jointFields μ z).V

def pathValueSize {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z : CriticalPath μ) : ℝ≥0∞ :=
  mixedNorm μ volume 10 10 (jointFields μ z).u

def pathEnergySize {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z : CriticalPath μ) : ℝ≥0∞ :=
  mixedNorm μ volume ∞ 6 (jointFields μ z).u

theorem joint_gradient_projection_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z : CriticalPath μ) :
    pathGradientSize μ z ≤ 6 * ENNReal.ofReal ‖fun j => criticalGradient μ j z‖ := by
  have hsum : (∑ j : Fin 3, ‖criticalGradient μ j z‖ₑ) ≤ 3 * ENNReal.ofReal ‖fun j => criticalGradient μ j z‖ := by
    calc
      _ ≤ ∑ _j : Fin 3, ENNReal.ofReal ‖fun j => criticalGradient μ j z‖ := Finset.sum_le_sum fun j _ =>
        (ofReal_norm (criticalGradient μ j z)).symm.le.trans
          (ENNReal.ofReal_le_ofReal (norm_le_pi_norm (fun j => criticalGradient μ j z) j))
      _ = _ := enorm_sum_three_const _
  have hU := joint_projection_mixed_bound μ z Complex.reCLM Complex.abs_re_le_norm _
    (jointFields μ z).joint_U.aestronglyMeasurable ((jointFields μ z).slice_eq.mono fun _ ht => ht.2.1)
  have hV := joint_projection_mixed_bound μ z Complex.imCLM Complex.abs_im_le_norm _
    (jointFields μ z).joint_V.aestronglyMeasurable ((jointFields μ z).slice_eq.mono fun _ ht => ht.2.2)
  exact (add_le_add (hU.trans hsum) (hV.trans hsum)).trans_eq (by ring)

theorem joint_gradient_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z : CriticalPath μ) :
    pathGradientSize μ z ≤ 6 * ENNReal.ofReal ‖z‖ :=
  (joint_gradient_projection_bound μ z).trans (mul_le_mul' le_rfl
    (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans_eq (criticalPath_norm μ z).symm)))

theorem joint_value_critical_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (z : CriticalPath μ) :
    pathValueSize μ z ≤ ENNReal.ofReal ((5/3)*K^(1/6 : ℝ)) * pathGradientSize μ z := by
  exact critical_mixedNorm_ten_bound hDensity hSob μ
    (jointFields μ z).u (jointFields μ z).U (jointFields μ z).V
    (jointFields μ z).joint_u.aestronglyMeasurable
    (jointFields μ z).joint_U.aestronglyMeasurable
    (jointFields μ z).joint_V.aestronglyMeasurable
    (jointFields μ z).inDotH1
    ((joint_gradient_memLp μ z).mono fun _ ht => ht.1)
    ((joint_gradient_memLp μ z).mono fun _ ht => ht.2)

theorem joint_value_difference_energy_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z w : CriticalPath μ) :
    mixedNorm μ volume ∞ 6 (fun t => (jointFields μ z).u t - (jointFields μ w).u t) ≤
      ENNReal.ofReal ‖z-w‖ := by
  exact (mixedNorm_congr_slices μ ∞ 6 ((joint_sub_slices μ z w).mono fun _ ht => ht.1)).symm.le.trans
    (joint_value_energy_bound μ (z-w))

theorem joint_gradient_difference_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (z w : CriticalPath μ) :
    mixedNorm μ volume 10 criticalExponent (fun t => (jointFields μ z).U t - (jointFields μ w).U t) +
    mixedNorm μ volume 10 criticalExponent (fun t => (jointFields μ z).V t - (jointFields μ w).V t) ≤
      6 * ENNReal.ofReal ‖z-w‖ := by
  have hU := mixedNorm_congr_slices μ 10 criticalExponent ((joint_sub_slices μ z w).mono fun _ ht => ht.2.1)
  have hV := mixedNorm_congr_slices μ 10 criticalExponent ((joint_sub_slices μ z w).mono fun _ ht => ht.2.2)
  exact (add_le_add hU.symm.le hV.symm.le).trans (joint_gradient_bound μ (z-w))

theorem joint_value_difference_critical_bound {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] (μ : Measure T) [SigmaFinite μ] (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (z w : CriticalPath μ) :
    mixedNorm μ volume 10 10 (fun t => (jointFields μ z).u t - (jointFields μ w).u t) ≤
      (ENNReal.ofReal ((5/3)*K^(1/6 : ℝ)) * 6) * ENNReal.ofReal ‖z-w‖ := by
  apply (mixedNorm_congr_slices μ 10 10 ((joint_sub_slices μ z w).mono fun _ ht => ht.1)).symm.le.trans
  exact (joint_value_critical_bound μ hDensity hSob (z-w)).trans
    ((mul_le_mul' le_rfl (joint_gradient_bound μ (z-w))).trans_eq (mul_assoc _ _ _).symm)
end HartreeF.CriticalSourceBounds
