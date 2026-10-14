import FLocalPathGradientFields
import FAffineIntervalEnergyPath

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter
open scoped ENNReal
namespace HartreeF.AffinePath
open EnergySpace TimeHolder CriticalPathSpace IntervalTimeTransport
open CriticalAffine AffineMixed AffineL1Source
attribute [local irreducible] energySubmodule

def affinePathGradientField {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
    (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))
    (j : Fin 3) : ℝ → Space → ℂ :=
  parabolicField a b c (3/2) (localPathGradientField (timeAffine_monotone ha c hAB) u j)

variable {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
  (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B))) (j : Fin 3)

theorem affinePathGradientField_joint :
    AEStronglyMeasurable (fun z : ℝ × Space => affinePathGradientField ha b c A B hAB u j z.1 z.2)
      ((localMeasure A B).prod volume) := by
  have h := parabolicField_jointly_measurable ha b c (3/2)
    (Icc (timeAffine a c A) (timeAffine a c B))
    (localPathGradientField (timeAffine_monotone ha c hAB) u j)
    (localPathGradientField_joint (timeAffine_monotone ha c hAB) u j).aestronglyMeasurable
  rw [timeAffine_preimage_Icc ha c A B] at h
  exact h

theorem affinePathGradientField_mixedNorm :
    mixedNorm (localMeasure A B) volume 10 criticalExponent (affinePathGradientField ha b c A B hAB u j)=
      ‖criticalGradient _ j u‖ₑ := by
  have h := parabolic_W_invariant ha b c (Icc (timeAffine a c A) (timeAffine a c B))
    (localPathGradientField (timeAffine_monotone ha c hAB) u j)
    (localPathGradientField_joint (timeAffine_monotone ha c hAB) u j).aestronglyMeasurable
  rw [timeAffine_preimage_Icc ha c A B] at h
  exact h.trans (localPathGradientField_mixedNorm (timeAffine_monotone ha c hAB) u j)

theorem affinePathGradientField_finite :
    mixedNorm (localMeasure A B) volume 10 criticalExponent (affinePathGradientField ha b c A B hAB u j)≠∞ := by
  rw [affinePathGradientField_mixedNorm ha b c A B hAB u j]
  exact enorm_ne_top

attribute [local irreducible] criticalPathSubmodule energyPath energyGradient
  affineState affineEnergyPath localPathGradientField

/-- Transport an actual weak-gradient representative before inserting a path. -/
theorem affine_gradient_representative_ae (v : EnergyState) (f : Space → ℂ)
    (hf : f =ᵐ[volume] (energyGradient j v : Space → ℂ)) :
    (fun x => a^(3/2:ℝ) • f (affine a b x)) =ᵐ[volume]
      (energyGradient j (affineState ha b v) : Space → ℂ) := by
  have hk : a*Real.sqrt a=a^(3/2:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = a^(1:ℝ)*a^(1/2:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ha]; norm_num
  filter_upwards [(affine_quasiMeasurePreserving ha.ne' b).ae_eq_comp hf,
    affineState_gradient_ae ha b v j] with x hx hg
  simp only [Function.comp_apply] at hx
  rw [hx]
  simpa only [gradientPullback,hk] using hg.symm

/-- The selected critical field is proved to represent the actual canonical
EnergyState gradient after affine transport. -/
theorem affinePathGradientField_energy_ae :
    ∀ᵐ (t : Icc A B) ∂intervalMeasure A B,
      affinePathGradientField ha b c A B hAB u j (t:ℝ) =ᵐ[volume]
        (energyGradient j (affineEnergyPath ha b c A B (energyPath _ u) t) : Space → ℂ) := by
  have hs := (timeAffine_quasiMeasurePreserving ha c
    (Icc (timeAffine a c A) (timeAffine a c B))).ae
    (localPathGradientField_energy_ae (timeAffine_monotone ha c hAB) u j)
  rw [timeAffine_preimage_Icc ha c A B] at hs
  have hi := (inclusion_measurePreserving A B).quasiMeasurePreserving.ae hs
  filter_upwards [hi] with t ht
  have hclamp : Set.projIcc (timeAffine a c A) (timeAffine a c B)
      (timeAffine_monotone ha c hAB) (timeAffine a c (t:ℝ))=
      intervalAffineHomeomorph ha c A B t :=
    Set.projIcc_val (timeAffine_monotone ha c hAB) (intervalAffineHomeomorph ha c A B t)
  rw [hclamp] at ht
  have h := affine_gradient_representative_ae ha b j
    (energyPath _ u (intervalAffineHomeomorph ha c A B t))
    (localPathGradientField (timeAffine_monotone ha c hAB) u j (timeAffine a c (t:ℝ))) ht
  rw [affineEnergyPath_apply]
  change (fun x => a^(3/2:ℝ) • localPathGradientField
    (timeAffine_monotone ha c hAB) u j (timeAffine a c (t:ℝ)) (affine a b x)) =ᵐ[volume] _ at h
  exact h

#print axioms affine_gradient_representative_ae

#print axioms affinePathGradientField
#print axioms affinePathGradientField_joint
#print axioms affinePathGradientField_mixedNorm
#print axioms affinePathGradientField_finite
#print axioms affinePathGradientField_energy_ae
end HartreeF.AffinePath
