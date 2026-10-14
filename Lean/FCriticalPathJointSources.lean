import FCriticalPathSpace
import FEnergyCriticalTimeConsumer
import FActualVectorDifferenceBound
import FActualGradientWeakTests

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.CriticalJointSources
open EnergySpace CriticalPathSpace CriticalTimeSobolev TimeHolder SobolevStretch
open StationarySelfTest GradientMajorants WeakHartreeProduct

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
  [BorelSpace T] (μ : Measure T) [SigmaFinite μ]

def jointFields (z : CriticalPath μ) : EnergyJointFields μ (energyPath μ z) :=
  energyJointFields μ (energyPath μ z) ((energyPath μ z).continuous.stronglyMeasurable_of_support_subset_isCompact
    isCompact_univ (Set.subset_univ _)).aestronglyMeasurable

theorem projected_critical_memLp (z : CriticalPath μ) (L : ℂ →L[ℝ] ℝ) :
    ∀ᵐ t ∂μ, MemLp (energyProjectedGradient L (energyPath μ z t)) criticalExponent volume := by
  filter_upwards [eventually_all.mpr (criticalGradient_memLp μ z)] with t ht
  apply memLp_finsetSum
  intro j _
  exact ((ht j).continuousLinearMap_comp L).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℝ (coordinate j))

theorem projected_critical_spatial_bound (z : CriticalPath μ) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ w, ‖L w‖ ≤ ‖w‖) (t : T) :
    eLpNorm (energyProjectedGradient L (energyPath μ z t)) criticalExponent volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j (energyPath μ z t)) criticalExponent volume := by
  calc
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x => L (energyGradient j (energyPath μ z t) x) • coordinate j)
        criticalExponent volume := by
      change eLpNorm (fun x => ∑ j : Fin 3, L (energyGradient j (energyPath μ z t) x) • coordinate j)
        criticalExponent volume ≤ _
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := (volume : Measure Space))
          (f := fun j : Fin 3 => fun x => L (energyGradient j (energyPath μ z t) x) • coordinate j)
          (by norm_num : (1 : ℝ≥0∞) ≤ criticalExponent))
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      apply eLpNorm_mono
        (((L.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).smul_const
          (coordinate j)))
      intro x
      simpa [norm_smul, coordinate] using hL (energyGradient j (energyPath μ z t) x)

theorem joint_projection_mixed_bound (z : CriticalPath μ) (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ w, ‖L w‖ ≤ ‖w‖) (F : T → Space → Space)
    (hF : AEStronglyMeasurable (fun tx : T × Space => F tx.1 tx.2) (μ.prod volume))
    (heq : ∀ᵐ t ∂μ, F t =ᵐ[volume] energyProjectedGradient L (energyPath μ z t)) :
    mixedNorm μ volume 10 criticalExponent F ≤
      ∑ j : Fin 3, ‖criticalGradient μ j z‖ₑ := by
  have hm := spatial_lp_time_measurable μ volume criticalExponent (by norm_num) (by norm_num) F hF
  have hs : ∀ᵐ t ∂μ, eLpNorm (F t) criticalExponent volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j (energyPath μ z t)) criticalExponent volume := by
    filter_upwards [heq] with t ht
    rw [eLpNorm_congr_ae ht]
    exact projected_critical_spatial_bound μ z L hL t
  unfold mixedNorm
  calc
    _ ≤ eLpNorm (fun t => ∑ j : Fin 3, eLpNorm (energyGradient j (energyPath μ z t))
        criticalExponent volume) 10 μ :=
      eLpNorm_mono_enorm_ae hm (by simpa only [enorm_eq_self] using hs)
    _ ≤ ∑ j : Fin 3, eLpNorm (fun t => eLpNorm (energyGradient j (energyPath μ z t))
        criticalExponent volume) 10 μ := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := μ)
          (f := fun j : Fin 3 => fun t => eLpNorm (energyGradient j (energyPath μ z t))
            criticalExponent volume) (by norm_num : (1 : ℝ≥0∞) ≤ 10))
    _ = _ := by simp only [criticalGradient_eLpNorm]

theorem joint_gradient_finite (z : CriticalPath μ) :
    mixedNorm μ volume 10 criticalExponent (jointFields μ z).U ≠ ∞ ∧
    mixedNorm μ volume 10 criticalExponent (jointFields μ z).V ≠ ∞ := by
  have hs : (∑ j : Fin 3, ‖criticalGradient μ j z‖ₑ) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun _ _ => enorm_ne_top)
  constructor
  · apply ne_top_of_le_ne_top hs
    exact joint_projection_mixed_bound μ z Complex.reCLM Complex.abs_re_le_norm _
      (jointFields μ z).joint_U.aestronglyMeasurable ((jointFields μ z).slice_eq.mono fun _ ht => ht.2.1)
  · apply ne_top_of_le_ne_top hs
    exact joint_projection_mixed_bound μ z Complex.imCLM Complex.abs_im_le_norm _
      (jointFields μ z).joint_V.aestronglyMeasurable ((jointFields μ z).slice_eq.mono fun _ ht => ht.2.2)

theorem joint_gradient_memLp (z : CriticalPath μ) :
    ∀ᵐ t ∂μ, MemLp ((jointFields μ z).U t) criticalExponent volume ∧
      MemLp ((jointFields μ z).V t) criticalExponent volume := by
  filter_upwards [(jointFields μ z).slice_eq,
    projected_critical_memLp μ z Complex.reCLM, projected_critical_memLp μ z Complex.imCLM]
    with t ht hR hI
  exact ⟨(memLp_congr_ae ht.2.1).mpr hR, (memLp_congr_ae ht.2.2).mpr hI⟩

theorem joint_value_critical (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (z : CriticalPath μ) :
    (∀ᵐ t ∂μ, MemLp ((jointFields μ z).u t) 10 volume) ∧
    mixedNorm μ volume 10 10 (jointFields μ z).u ≠ ∞ := by
  have h := critical_mixedNorm_ten_finite_and_bound hDensity hSob μ
    (jointFields μ z).u (jointFields μ z).U (jointFields μ z).V
    (jointFields μ z).joint_u.aestronglyMeasurable
    (jointFields μ z).joint_U.aestronglyMeasurable
    (jointFields μ z).joint_V.aestronglyMeasurable
    (jointFields μ z).inDotH1
    ((joint_gradient_memLp μ z).mono fun _ ht => ht.1)
    ((joint_gradient_memLp μ z).mono fun _ ht => ht.2)
    (joint_gradient_finite μ z).1 (joint_gradient_finite μ z).2
  exact ⟨h.1, h.2.1⟩

end HartreeF.CriticalJointSources
