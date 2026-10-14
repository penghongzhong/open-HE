import FAffinePathGradientFields

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.AffinePath
open EnergySpace TimeHolder CriticalPathSpace IntervalTimeTransport AffineMixed CriticalAffine

/-- The actual local homogeneous-energy path, with its constructed critical
Bochner coordinates and proved representative compatibility. -/
def affineCriticalPath {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
    (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B))) :
    CriticalPath (intervalMeasure A B) :=
  criticalPathOfLocalFields A B (affineEnergyPath ha b c A B (energyPath _ u))
    (affinePathGradientField ha b c A B hAB u)
    (affinePathGradientField_joint ha b c A B hAB u)
    (affinePathGradientField_finite ha b c A B hAB u)
    (affinePathGradientField_energy_ae ha b c A B hAB u)

variable {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
  (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))

@[simp] theorem affineCriticalPath_energy :
    energyPath _ (affineCriticalPath ha b c A B hAB u)=
      affineEnergyPath ha b c A B (energyPath _ u) := rfl

@[simp] theorem affineCriticalPath_energy_apply (t : Icc A B) :
    energyPath _ (affineCriticalPath ha b c A B hAB u) t=
      affineState ha b (energyPath _ u (intervalAffineHomeomorph ha c A B t)) := rfl

attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  criticalPathOfLocalFields affinePathGradientField

theorem affineCriticalPath_gradient_norm (j : Fin 3) :
    ‖criticalGradient _ j (affineCriticalPath ha b c A B hAB u)‖=‖criticalGradient _ j u‖ := by
  unfold affineCriticalPath
  rw [criticalPathOfLocalFields_gradient_norm,affinePathGradientField_mixedNorm]
  exact toReal_enorm _

attribute [local irreducible] affineCriticalPath

/-- The full actual path graph norm is preserved, including the continuous
energy supremum on a single-point interval. -/
theorem affineCriticalPath_norm : ‖affineCriticalPath ha b c A B hAB u‖=‖u‖ := by
  let v := affineCriticalPath ha b c A B hAB u
  have hj (j : Fin 3) : ‖criticalGradient _ j v‖=‖criticalGradient _ j u‖ :=
    affineCriticalPath_gradient_norm ha b c A B hAB u j
  have hp : ‖fun j : Fin 3 => criticalGradient _ j v‖=‖fun j : Fin 3 => criticalGradient _ j u‖ := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      rw [hj j]
      exact norm_le_pi_norm (fun j : Fin 3 => criticalGradient _ j u) j
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      rw [← hj j]
      exact norm_le_pi_norm (fun j : Fin 3 => criticalGradient _ j v) j
  have he : ‖energyPath _ v‖=‖energyPath _ u‖ :=
    (congrArg norm (affineCriticalPath_energy ha b c A B hAB u)).trans
      (affineEnergyPath_norm ha b c A B (energyPath _ u))
  calc
    ‖v‖ = max ‖energyPath _ v‖ ‖fun j : Fin 3 => criticalGradient _ j v‖ := criticalPath_norm _ v
    _ = max ‖energyPath _ u‖ ‖fun j : Fin 3 => criticalGradient _ j u‖ := congrArg₂ max he hp
    _ = ‖u‖ := (criticalPath_norm _ u).symm


#print axioms affineCriticalPath
#print axioms affineCriticalPath_energy
#print axioms affineCriticalPath_energy_apply
#print axioms affineCriticalPath_gradient_norm
#print axioms affineCriticalPath_norm
end HartreeF.AffinePath
