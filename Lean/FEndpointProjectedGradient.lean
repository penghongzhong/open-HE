import FEndpointHartreeDuhamelOutput

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.EndpointOutput
open MeasureTheory Filter TimeHolder EnergySpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathSpace SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
open scoped ENNReal NNReal
attribute [local irreducible] CriticalJointSources.jointFields

variable {T : Type*} [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]
  {g : T → EnergyState}

theorem endpoint_projected_spatial_bound (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ w, ‖L w‖ ≤ ‖w‖) (u : EnergyState) :
    eLpNorm (energyProjectedGradient L u) 6 volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j u) 6 volume := by
  calc
    _ ≤ ∑ j : Fin 3, eLpNorm (fun x => L (energyGradient j u x) • coordinate j) 6 volume := by
      change eLpNorm (fun x => ∑ j : Fin 3, L (energyGradient j u x) • coordinate j) 6 volume ≤ _
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := (volume : Measure Space))
          (f := fun j : Fin 3 => fun x => L (energyGradient j u x) • coordinate j)
          (by norm_num : (1 : ℝ≥0∞) ≤ 6))
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      apply eLpNorm_mono
        ((L.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).smul_const
          (coordinate j))
      intro x
      simpa [norm_smul, coordinate] using hL (energyGradient j u x)

/-- Actual joint real/imaginary gradients receive the endpoint bound from the
constructed complex coordinate witnesses. -/
theorem EndpointGradientWitness.projected_joint_bound (W : EndpointGradientWitness μ g)
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ w, ‖L w‖ ≤ ‖w‖) (F : T → Space → Space)
    (hF : AEStronglyMeasurable (fun tx : T × Space => F tx.1 tx.2) (μ.prod volume))
    (heq : ∀ᵐ t ∂μ, F t =ᵐ[volume] energyProjectedGradient L (g t)) :
    mixedNorm μ volume 2 6 F ≤ ∑ j : Fin 3, ‖W.field j‖ₑ := by
  have hm := spatial_lp_time_measurable μ volume 6 (by norm_num) (by norm_num) F hF
  have hs : ∀ᵐ t ∂μ, eLpNorm (F t) 6 volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j (g t)) 6 volume := by
    filter_upwards [heq] with t ht
    rw [eLpNorm_congr_ae ht]
    exact endpoint_projected_spatial_bound L hL (g t)
  unfold mixedNorm
  calc
    _ ≤ eLpNorm (fun t => ∑ j : Fin 3, eLpNorm (energyGradient j (g t)) 6 volume) 2 μ :=
      eLpNorm_mono_enorm_ae hm (by simpa only [enorm_eq_self] using hs)
    _ ≤ ∑ j : Fin 3, eLpNorm (fun t => eLpNorm (energyGradient j (g t)) 6 volume) 2 μ := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := μ)
          (f := fun j : Fin 3 => fun t => eLpNorm (energyGradient j (g t)) 6 volume)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    _ = _ := by simp only [← W.mixedNorm_eq, mixedNorm]

theorem fullZPath_joint_gradient_endpoint_finite {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) (hu : FullZPath u) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (CriticalJointSources.jointFields (intervalMeasure a b) u).U ≠ ∞ ∧
    mixedNorm (intervalMeasure a b) volume 2 6
      (CriticalJointSources.jointFields (intervalMeasure a b) u).V ≠ ∞ := by
  obtain ⟨W⟩ := hu
  have hs : (∑ j : Fin 3, ‖W.field j‖ₑ) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun _ _ => enorm_ne_top)
  constructor
  · apply ne_top_of_le_ne_top hs
    exact W.projected_joint_bound Complex.reCLM Complex.abs_re_le_norm _
      (CriticalJointSources.jointFields _ u).joint_U.aestronglyMeasurable
      ((CriticalJointSources.jointFields _ u).slice_eq.mono fun _ ht => ht.2.1)
  · apply ne_top_of_le_ne_top hs
    exact W.projected_joint_bound Complex.imCLM Complex.abs_im_le_norm _
      (CriticalJointSources.jointFields _ u).joint_V.aestronglyMeasurable
      ((CriticalJointSources.jointFields _ u).slice_eq.mono fun _ ht => ht.2.2)

theorem fullZPath_actual_gradient_endpoint_finite {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) (hu : FullZPath u) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient Complex.reCLM (energyPath _ u t)) ≠ ∞ ∧
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient Complex.imCLM (energyPath _ u t)) ≠ ∞ := by
  have heR : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient Complex.reCLM (energyPath _ u t)) =
      mixedNorm (intervalMeasure a b) volume 2 6
        (CriticalJointSources.jointFields (intervalMeasure a b) u).U := by
    apply eLpNorm_congr_ae
    filter_upwards [(CriticalJointSources.jointFields (intervalMeasure a b) u).slice_eq]
      with t ht
    exact eLpNorm_congr_ae ht.2.1.symm
  have heI : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyProjectedGradient Complex.imCLM (energyPath _ u t)) =
      mixedNorm (intervalMeasure a b) volume 2 6
        (CriticalJointSources.jointFields (intervalMeasure a b) u).V := by
    apply eLpNorm_congr_ae
    filter_upwards [(CriticalJointSources.jointFields (intervalMeasure a b) u).slice_eq]
      with t ht
    exact eLpNorm_congr_ae ht.2.2.symm
  have hfin := fullZPath_joint_gradient_endpoint_finite u hu
  exact ⟨fun ht => hfin.1 (heR.symm.trans ht), fun ht => hfin.2 (heI.symm.trans ht)⟩

end HartreeF.EndpointOutput
