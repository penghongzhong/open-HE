import FCriticalAffineGeometry
import FTimeFiniteNormBridge
import Mathlib.MeasureTheory.Measure.Restrict

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped ENNReal Topology
namespace HartreeF.AffineMixed
open CriticalAffine TimeHolder

def timeAffine (a c t : ℝ) : ℝ := a^2*t+c

def timeAffineHomeomorph {a : ℝ} (ha : 0<a) (c : ℝ) : ℝ ≃ₜ ℝ where
  toFun := timeAffine a c
  invFun := fun t => (t-c)/a^2
  left_inv := by intro t; unfold timeAffine; field_simp; ring
  right_inv := by intro t; unfold timeAffine; field_simp; ring
  continuous_toFun := by unfold timeAffine; fun_prop
  continuous_invFun := by fun_prop

/-- Exact positive 3D spatial affine Jacobian, as a measure pushforward. -/
theorem affine_map_volume {a : ℝ} (ha : 0<a) (b : Space) :
    Measure.map (affine a b) volume=ENNReal.ofReal ((a^3)⁻¹) • (volume : Measure Space) := by
  change Measure.map ((fun x : Space => x+b) ∘ (fun x : Space => a • x)) volume=_
  have hadd : Measurable (fun x : Space => x+b) := by fun_prop
  have hmul : Measurable (fun x : Space => a • x) := by fun_prop
  rw [← Measure.map_map hadd hmul,
    Measure.map_addHaar_smul volume ha.ne', Measure.map_smul (hf := hadd.aemeasurable),
    (measurePreserving_add_right volume b).map_eq]
  congr 1
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [abs_of_pos (inv_pos.mpr (pow_pos ha 3))]

/-- Positive a gives the time Jacobian a^(-2), with no reversal of intervals. -/
theorem timeAffine_map_volume {a : ℝ} (ha : 0<a) (c : ℝ) :
    Measure.map (timeAffine a c) volume=ENNReal.ofReal ((a^2)⁻¹) • (volume : Measure ℝ) := by
  change Measure.map ((fun t : ℝ => t+c) ∘ (fun t : ℝ => a^2 • t)) volume=_
  have hadd : Measurable (fun t : ℝ => t+c) := by fun_prop
  have hmul : Measurable (fun t : ℝ => a^2 • t) := by fun_prop
  rw [← Measure.map_map hadd hmul,
    Measure.map_addHaar_smul volume (pow_ne_zero 2 ha.ne'), Measure.map_smul (hf := hadd.aemeasurable),
    (measurePreserving_add_right volume c).map_eq]
  congr 1
  simp only [Module.finrank_self, pow_one]
  rw [abs_of_pos (inv_pos.mpr (pow_pos ha 2))]

/-- The exact same pushforward on restricted time, rather than an assumed
whole-line norm or a silently changed integration interval. -/
theorem timeAffine_map_restrict {a : ℝ} (ha : 0<a) (c : ℝ) (S : Set ℝ) :
    Measure.map (timeAffine a c) (volume.restrict ((timeAffine a c) ⁻¹' S))=
      ENNReal.ofReal ((a^2)⁻¹) • (volume.restrict S) := by
  have h := (timeAffineHomeomorph ha c).toMeasurableEquiv.restrict_map volume S
  change (Measure.map (timeAffine a c) volume).restrict S=
    Measure.map (timeAffine a c) (volume.restrict ((timeAffine a c) ⁻¹' S)) at h
  rw [← h,timeAffine_map_volume ha c,Measure.restrict_smul]

theorem timeAffine_preimage_Icc {a : ℝ} (ha : 0<a) (c A B : ℝ) :
    (timeAffine a c) ⁻¹' Icc (timeAffine a c A) (timeAffine a c B)=Icc A B := by
  ext t
  simp only [mem_preimage,mem_Icc,timeAffine,add_le_add_iff_right,
    mul_le_mul_iff_right₀ (pow_pos ha 2)]

#print axioms timeAffine
#print axioms timeAffineHomeomorph
#print axioms affine_map_volume
#print axioms timeAffine_map_volume
#print axioms timeAffine_map_restrict
#print axioms timeAffine_preimage_Icc
end HartreeF.AffineMixed
