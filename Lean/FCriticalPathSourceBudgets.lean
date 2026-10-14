import FCriticalPathJointSources

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000
set_option linter.unusedSectionVars false
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.CriticalJointSources
open EnergySpace CriticalPathSpace CriticalTimeSobolev TimeHolder SobolevStretch
open StationarySelfTest ForcingDomain GradientMajorants WeakHartreeProduct
attribute [local irreducible] jointFields

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
  [BorelSpace T] (μ : Measure T) [SigmaFinite μ]

theorem joint_value_energy_finite (z : CriticalPath μ) :
    mixedNorm μ volume ∞ 6 (jointFields μ z).u ≠ ∞ := by
  have hm := spatial_lp_time_measurable μ volume 6 (by norm_num) (by norm_num)
    (jointFields μ z).u (jointFields μ z).joint_u.aestronglyMeasurable
  have hb : ∀ᵐ t ∂μ, ‖eLpNorm ((jointFields μ z).u t) 6 volume‖ₑ ≤ ENNReal.ofReal ‖z‖ := by
    filter_upwards [(jointFields μ z).slice_eq] with t ht
    have he : eLpNorm ((jointFields μ z).u t) 6 volume =
        ‖energyValue (energyPath μ z t)‖ₑ :=
      (eLpNorm_congr_ae ht.1).trans (Lp.enorm_def (energyValue (energyPath μ z t))).symm
    calc
      _ = ‖energyValue (energyPath μ z t)‖ₑ := by simpa only [enorm_eq_self] using he
      _ = ENNReal.ofReal ‖energyValue (energyPath μ z t)‖ :=
        (ofReal_norm (energyValue (energyPath μ z t))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        ((energyState_value_norm_le (energyPath μ z t)).trans (energyPath_value_norm_le μ z t))
  unfold mixedNorm
  rw [eLpNorm_exponent_top hm]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_enorm_bound hb)

theorem mixedNorm_sub_finite {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) (hqtop : q ≠ ∞)
    (f g : T → Space → E)
    (hf : AEStronglyMeasurable (fun tx : T × Space => f tx.1 tx.2) (μ.prod volume))
    (hg : AEStronglyMeasurable (fun tx : T × Space => g tx.1 tx.2) (μ.prod volume))
    (hff : mixedNorm μ volume p q f ≠ ∞) (hgf : mixedNorm μ volume p q g ≠ ∞) :
    mixedNorm μ volume p q (fun t => f t - g t) ≠ ∞ := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hff, hgf⟩)
  apply mixed_norm_le_add_of_domination μ p q hp hq hqtop
    (fun t => f t - g t) f g (hf.sub hg) hf hg
  exact Eventually.of_forall fun t => Eventually.of_forall fun x => norm_sub_le (f t x) (g t x)

theorem joint_slices (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (z w : CriticalPath μ) :
    ∀ᵐ t ∂μ,
      InDotH1 ((jointFields μ z).u t) ((jointFields μ z).U t) ((jointFields μ z).V t) ∧
      InDotH1 ((jointFields μ w).u t) ((jointFields μ w).U t) ((jointFields μ w).V t) ∧
      MemLp ((jointFields μ z).u t) 10 volume ∧ MemLp ((jointFields μ w).u t) 10 volume ∧
      MemLp ((jointFields μ z).U t) CriticalPathSpace.criticalExponent volume ∧
      MemLp ((jointFields μ z).V t) CriticalPathSpace.criticalExponent volume ∧
      MemLp ((jointFields μ w).U t) CriticalPathSpace.criticalExponent volume ∧
      MemLp ((jointFields μ w).V t) CriticalPathSpace.criticalExponent volume := by
  filter_upwards [(jointFields μ z).inDotH1, (jointFields μ w).inDotH1,
    (joint_value_critical μ hDensity hSob z).1, (joint_value_critical μ hDensity hSob w).1,
    joint_gradient_memLp μ z, joint_gradient_memLp μ w] with t hz hw hzu hwu hzG hwG
  exact ⟨hz, hw, hzu, hwu, hzG.1, hzG.2, hwG.1, hwG.2⟩

theorem joint_vectorBudget_finite (hDensity : OrdinaryH1Density) {K alpha : ℝ}
    (hSob : OrdinarySobolev K) (ha : 0 < alpha) (ha3 : alpha < 3) (z w : CriticalPath μ) :
    vectorDifferenceBudget alpha μ (jointFields μ z).u (jointFields μ w).u
      (jointFields μ z).U (jointFields μ z).V (jointFields μ w).U (jointFields μ w).V ≠ ∞ := by
  have hM1 := joint_value_energy_finite μ z
  have hM2 := joint_value_energy_finite μ w
  have hN1 := (joint_value_critical μ hDensity hSob z).2
  have hN2 := (joint_value_critical μ hDensity hSob w).2
  have hG1 := joint_gradient_finite μ z
  have hG2 := joint_gradient_finite μ w
  have hD := mixedNorm_sub_finite μ ∞ 6 (by norm_num) (by norm_num) (by norm_num)
    (jointFields μ z).u (jointFields μ w).u (jointFields μ z).joint_u.aestronglyMeasurable
    (jointFields μ w).joint_u.aestronglyMeasurable hM1 hM2
  have hE := mixedNorm_sub_finite μ 10 10 (by norm_num) (by norm_num) (by norm_num)
    (jointFields μ z).u (jointFields μ w).u (jointFields μ z).joint_u.aestronglyMeasurable
    (jointFields μ w).joint_u.aestronglyMeasurable hN1 hN2
  have hZ1 := mixedNorm_sub_finite μ 10 CriticalPathSpace.criticalExponent (by norm_num) (by norm_num) (by norm_num)
    (jointFields μ z).U (jointFields μ w).U (jointFields μ z).joint_U.aestronglyMeasurable
    (jointFields μ w).joint_U.aestronglyMeasurable hG1.1 hG2.1
  have hZ2 := mixedNorm_sub_finite μ 10 CriticalPathSpace.criticalExponent (by norm_num) (by norm_num) (by norm_num)
    (jointFields μ z).V (jointFields μ w).V (jointFields μ z).joint_V.aestronglyMeasurable
    (jointFields μ w).joint_V.aestronglyMeasurable hG1.2 hG2.2
  have ht : 0 ≤ theta alpha := by unfold theta; linarith
  have h4t : 0 ≤ 4 - theta alpha := by unfold theta; linarith
  have hM := ENNReal.add_ne_top.mpr ⟨hM1, hM2⟩
  have hN := ENNReal.add_ne_top.mpr ⟨hN1, hN2⟩
  have hY := ENNReal.add_ne_top.mpr ⟨hG2.1, hG2.2⟩
  have hZ := ENNReal.add_ne_top.mpr ⟨hZ1, hZ2⟩
  have h2a := ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ 2 * alpha) hM
  have h5a := ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ 5 * alpha / 3) hM
  have h4 := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) hN
  have h3 := ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) hN
  have h4theta := ENNReal.rpow_ne_top_of_nonneg h4t hN
  have hda := ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ alpha / 3) hD
  have het := ENNReal.rpow_ne_top_of_nonneg ht hE
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top h2a h4) hZ,
     ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h2a h3) hY) hE⟩,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top h5a h4theta) hY) hda) het⟩

end HartreeF.CriticalJointSources
