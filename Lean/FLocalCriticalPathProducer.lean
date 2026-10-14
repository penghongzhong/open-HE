import FParabolicCompatibleL1Source
import FJointLpRealization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ENNReal
namespace HartreeF.AffinePath
open EnergySpace TimeHolder CriticalPathSpace IntervalTimeTransport

local instance : Fact (criticalExponent≠∞) := ⟨by norm_num [criticalExponent]⟩

/-- Local joint fields construct the actual path graph, with no whole-line
critical norm or whole-line representative-agreement premise. -/
def criticalPathOfLocalFields (A B : ℝ) (g : C(Icc A B,EnergyState))
    (d : Fin 3 → ℝ → Space → ℂ)
    (hdm : ∀ j, AEStronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2)
      ((localMeasure A B).prod volume))
    (hdf : ∀ j, mixedNorm (localMeasure A B) volume 10 criticalExponent (d j)≠∞)
    (hd : ∀ j, ∀ᵐ (t : Icc A B) ∂intervalMeasure A B,
      d j (t:ℝ) =ᵐ[volume] (energyGradient j (g t) : Space → ℂ)) :
    CriticalPath (intervalMeasure A B) := by
  have hs (j : Fin 3) : ∀ᵐ t ∂localMeasure A B, MemLp (d j t) criticalExponent volume :=
    finite_mixedNorm_ae_slice_memLp (localMeasure A B) volume 10 criticalExponent
      (by norm_num) (by norm_num [criticalExponent]) (d j) (hdf j)
  let D (j : Fin 3) := jointLpRealization (localMeasure A B) volume 10 criticalExponent
    (fun z : ℝ × Space => d j z.1 z.2) (hdm j) (hs j) (hdf j)
  refine ofRepresentativeAgreement (intervalMeasure A B) g
    (fun j => toIntervalLp A B 10 (D j)) ?_
  intro j
  have hj := (inclusion_measurePreserving A B).quasiMeasurePreserving.ae
    (jointLpRealization_coeFn (localMeasure A B) volume 10 criticalExponent
      (fun z : ℝ × Space => d j z.1 z.2) (hdm j) (hs j) (hdf j))
  filter_upwards [hd j,hj,toIntervalLp_coeFn A B 10 (D j)] with t ht hdt hD
  rw [hD]
  have hdt' : (D j (t:ℝ) : Space → ℂ) =ᵐ[volume] d j (t:ℝ) := hdt
  exact ht.symm.trans hdt'.symm

@[simp] theorem criticalPathOfLocalFields_energy (A B : ℝ) (g : C(Icc A B,EnergyState))
    (d : Fin 3 → ℝ → Space → ℂ)
    (hdm : ∀ j, AEStronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2)
      ((localMeasure A B).prod volume))
    (hdf : ∀ j, mixedNorm (localMeasure A B) volume 10 criticalExponent (d j)≠∞)
    (hd : ∀ j, ∀ᵐ (t : Icc A B) ∂intervalMeasure A B,
      d j (t:ℝ) =ᵐ[volume] (energyGradient j (g t) : Space → ℂ)) :
    energyPath _ (criticalPathOfLocalFields A B g d hdm hdf hd)=g := rfl

theorem criticalPathOfLocalFields_gradient_norm (A B : ℝ) (g : C(Icc A B,EnergyState))
    (d : Fin 3 → ℝ → Space → ℂ)
    (hdm : ∀ j, AEStronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2)
      ((localMeasure A B).prod volume))
    (hdf : ∀ j, mixedNorm (localMeasure A B) volume 10 criticalExponent (d j)≠∞)
    (hd : ∀ j, ∀ᵐ (t : Icc A B) ∂intervalMeasure A B,
      d j (t:ℝ) =ᵐ[volume] (energyGradient j (g t) : Space → ℂ)) (j : Fin 3) :
    ‖criticalGradient _ j (criticalPathOfLocalFields A B g d hdm hdf hd)‖=
      (mixedNorm (localMeasure A B) volume 10 criticalExponent (d j)).toReal := by
  change ‖toIntervalLp A B 10 _‖=_
  rw [toIntervalLp_norm]
  exact jointLpRealization_norm _ _ _ _ _ _ _ _

#print axioms criticalPathOfLocalFields
#print axioms criticalPathOfLocalFields_energy
#print axioms criticalPathOfLocalFields_gradient_norm
end HartreeF.AffinePath
