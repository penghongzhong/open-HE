import FLocalCriticalPathProducer
import FJointLpRepresentatives

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ENNReal
namespace HartreeF.AffinePath
open EnergySpace TimeHolder CriticalPathSpace IntervalTimeTransport

/-- Select a joint representative of the EXISTING critical Bochner coordinate.
It is defined on real time, but all norm hypotheses remain interval-local. -/
def localPathGradientField {A B : ℝ} (hAB : A≤B)
    (u : CriticalPath (intervalMeasure A B)) (j : Fin 3) : ℝ → Space → ℂ :=
  fun t x => aeJointLpRepresentative (localMeasure A B) volume criticalExponent
    (toLocalLp hAB 10 (criticalGradient _ j u)) (Lp.aestronglyMeasurable _) (t,x)

theorem localPathGradientField_joint {A B : ℝ} (hAB : A≤B)
    (u : CriticalPath (intervalMeasure A B)) (j : Fin 3) :
    StronglyMeasurable (fun z : ℝ × Space => localPathGradientField hAB u j z.1 z.2) :=
  aeJointLpRepresentative_stronglyMeasurable _ _ _ _ _

theorem localPathGradientField_class_ae {A B : ℝ} (hAB : A≤B)
    (u : CriticalPath (intervalMeasure A B)) (j : Fin 3) :
    ∀ᵐ t ∂localMeasure A B, localPathGradientField hAB u j t =ᵐ[volume]
      (toLocalLp hAB 10 (criticalGradient _ j u) t : Space → ℂ) :=
  aeJointLpRepresentative_slice _ _ _ _ _

theorem localPathGradientField_energy_ae {A B : ℝ} (hAB : A≤B)
    (u : CriticalPath (intervalMeasure A B)) (j : Fin 3) :
    ∀ᵐ t ∂localMeasure A B, localPathGradientField hAB u j t =ᵐ[volume]
      (energyGradient j (energyPath _ u (Set.projIcc A B hAB t)) : Space → ℂ) := by
  filter_upwards [localPathGradientField_class_ae hAB u j,
    toLocalLp_coeFn hAB 10 (criticalGradient _ j u),
    ae_clamp hAB (criticalGradient_ae_eq _ u j)] with t ht hLp hg
  rw [hLp] at ht
  exact ht.trans hg.symm

/-- Exact existing coordinate norm, not a new numerical W input. -/
theorem localPathGradientField_mixedNorm {A B : ℝ} (hAB : A≤B)
    (u : CriticalPath (intervalMeasure A B)) (j : Fin 3) :
    mixedNorm (localMeasure A B) volume 10 criticalExponent (localPathGradientField hAB u j)=
      ‖criticalGradient _ j u‖ₑ := by
  calc
    _ = eLpNorm (fun t => ‖toLocalLp hAB 10 (criticalGradient _ j u) t‖ₑ) 10 (localMeasure A B) := by
      apply eLpNorm_congr_ae
      filter_upwards [localPathGradientField_class_ae hAB u j] with t ht
      exact (eLpNorm_congr_ae ht).trans (Lp.enorm_def _).symm
    _ = eLpNorm (toLocalLp hAB 10 (criticalGradient _ j u)) 10 (localMeasure A B) :=
      eLpNorm_enorm _ (Lp.aestronglyMeasurable _)
    _ = ‖toLocalLp hAB 10 (criticalGradient _ j u)‖ₑ := (Lp.enorm_def _).symm
    _ = _ := by
      simpa only [ofReal_norm] using congrArg ENNReal.ofReal
        (toLocalLp_norm hAB 10 (criticalGradient _ j u))

theorem localPathGradientField_finite {A B : ℝ} (hAB : A≤B)
    (u : CriticalPath (intervalMeasure A B)) (j : Fin 3) :
    mixedNorm (localMeasure A B) volume 10 criticalExponent (localPathGradientField hAB u j)≠∞ := by
  rw [localPathGradientField_mixedNorm hAB u j]
  exact enorm_ne_top

#print axioms localPathGradientField
#print axioms localPathGradientField_joint
#print axioms localPathGradientField_class_ae
#print axioms localPathGradientField_energy_ae
#print axioms localPathGradientField_mixedNorm
#print axioms localPathGradientField_finite
end HartreeF.AffinePath
