import FAffineMeasurePushforward
import FCriticalAffineIsometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.AffinePath
open EnergySpace AffineMixed CriticalAffine

theorem timeAffine_monotone {a : ℝ} (ha : 0<a) (c : ℝ) : Monotone (timeAffine a c) := by
  intro A B hAB
  exact add_le_add_left (mul_le_mul_of_nonneg_left hAB (pow_pos ha 2).le) c

/-- The positive time scaling is an actual interval homeomorphism, including
single-point and empty intervals. -/
def intervalAffineHomeomorph {a : ℝ} (ha : 0<a) (c A B : ℝ) :
    Icc A B ≃ₜ Icc (timeAffine a c A) (timeAffine a c B) where
  toFun := fun t => ⟨timeAffine a c t, by
    exact ⟨timeAffine_monotone ha c t.property.1,timeAffine_monotone ha c t.property.2⟩⟩
  invFun := fun s => ⟨(timeAffineHomeomorph ha c).symm s, by
    rw [← timeAffine_preimage_Icc ha c A B]
    change timeAffine a c ((timeAffineHomeomorph ha c).symm s) ∈
      Icc (timeAffine a c A) (timeAffine a c B)
    have he : timeAffine a c ((timeAffineHomeomorph ha c).symm s)=(s:ℝ) :=
      (timeAffineHomeomorph ha c).apply_symm_apply s
    rw [he]
    exact s.property⟩
  left_inv := by
    intro t
    apply Subtype.ext
    exact (timeAffineHomeomorph ha c).symm_apply_apply (t:ℝ)
  right_inv := by
    intro s
    apply Subtype.ext
    exact (timeAffineHomeomorph ha c).apply_symm_apply (s:ℝ)
  continuous_toFun := ((timeAffineHomeomorph ha c).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((timeAffineHomeomorph ha c).symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem intervalAffineHomeomorph_coe {a : ℝ} (ha : 0<a) (c A B : ℝ) (t : Icc A B) :
    (intervalAffineHomeomorph ha c A B t : ℝ)=timeAffine a c t := rfl

def affineEnergyPath {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ)
    (u : C(Icc (timeAffine a c A) (timeAffine a c B),EnergyState)) : C(Icc A B,EnergyState) :=
  ⟨fun t => affineState ha b (u (intervalAffineHomeomorph ha c A B t)),
    (affineStateEquiv ha b).continuous.comp
      (u.continuous.comp (intervalAffineHomeomorph ha c A B).continuous)⟩

@[simp] theorem affineEnergyPath_apply {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ)
    (u : C(Icc (timeAffine a c A) (timeAffine a c B),EnergyState)) (t : Icc A B) :
    affineEnergyPath ha b c A B u t=
      affineState ha b (u (intervalAffineHomeomorph ha c A B t)) := rfl

/-- The genuine continuous-curve supremum is preserved by the interval
bijection. No replacement by essential supremum on a zero-measure interval. -/
theorem affineEnergyPath_norm {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ)
    (u : C(Icc (timeAffine a c A) (timeAffine a c B),EnergyState)) :
    ‖affineEnergyPath ha b c A B u‖=‖u‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
    intro t
    rw [affineEnergyPath_apply,affineState_norm]
    exact u.norm_coe_le_norm _
  · apply (ContinuousMap.norm_le _ (norm_nonneg (affineEnergyPath ha b c A B u))).mpr
    intro s
    have ht := (affineEnergyPath ha b c A B u).norm_coe_le_norm
      ((intervalAffineHomeomorph ha c A B).symm s)
    rw [affineEnergyPath_apply,(intervalAffineHomeomorph ha c A B).apply_symm_apply,
      affineState_norm] at ht
    exact ht

#print axioms timeAffine_monotone
#print axioms intervalAffineHomeomorph
#print axioms intervalAffineHomeomorph_coe
#print axioms affineEnergyPath
#print axioms affineEnergyPath_apply
#print axioms affineEnergyPath_norm
end HartreeF.AffinePath
