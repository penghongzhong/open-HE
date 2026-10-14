import Lemma_4_1_WeightedH1
import Mathlib.MeasureTheory.Group.Integral

/-! Actual translation of the weak derivative and of all integrals.
This proves the arbitrary-center form of (14), without a translation interface. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

local instance : (volume : Measure Plane).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance
local instance : (volume : Measure Space).IsAddHaarMeasure := by
  change ((volume : Measure ℝ).prod (volume : Measure Plane)).IsAddHaarMeasure
  infer_instance

theorem InH1.translate {u : Space → ℝ} {D : Space → Space →L[ℝ] ℝ}
    (hu : InH1 u D) (a : Space) : InH1 (fun z => u (z+a)) (fun z => D (z+a)) := by
  refine ⟨hu.1.comp_measurePreserving (measurePreserving_add_right volume a),
    hu.2.1.comp_measurePreserving (measurePreserving_add_right volume a),?_⟩
  intro e φ hφ hc
  have hψ : ContDiff ℝ ∞ (fun z => φ (z-a)) := hφ.comp (contDiff_id.sub contDiff_const)
  have hcψ : HasCompactSupport (fun z => φ (z-a)) := by
    simpa only [Function.comp_def,Homeomorph.coe_addRight,sub_eq_add_neg] using
      hc.comp_homeomorph (Homeomorph.addRight (-a))
  have h := hu.2.2 e (fun z => φ (z-a)) hψ hcψ
  simp_rw [fderiv_comp_sub] at h
  have hL := integral_add_right_eq_self (μ := volume) (fun z => u z*fderiv ℝ φ (z-a) e) a
  have hR := integral_add_right_eq_self (μ := volume) (fun z => D z e*φ (z-a)) a
  simp only [add_sub_cancel_right] at hL hR
  rw [hL,hR]
  exact h

def centeredWeight (b : ℝ → ℝ) (a : Plane) (z : Space) : ℝ :=
  radialWeight b (z-(0,a))

theorem centeredWeight_add (b : ℝ → ℝ) (a : Plane) (z : Space) :
    centeredWeight b a (z+(0,a)) = radialWeight b z := by
  simp only [centeredWeight,add_sub_cancel_right]

theorem centeredWeight_integral (b : ℝ → ℝ) (a : Plane) (F : Space → ℝ) :
    (∫ z,radialWeight b z*F (z+(0,a))) = ∫ z,centeredWeight b a z*F z := by
  have h := integral_add_right_eq_self (μ := volume) (fun z => centeredWeight b a z*F z) (0,a)
  simpa only [centeredWeight_add] using h

/-- The arbitrary transverse-center form of the full H1 estimate (14). -/
theorem centeredWeight_anisotropic_H1 {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback)
    (glue : SmoothInterfaceGluing) (density : SmoothH1MomentDensity)
    {u : Space → ℝ} {D : Space → Space →L[ℝ] ℝ} (hu : InH1 u D)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbound : ∃ M,∀ r,0 ≤ r → b r ≤ M) (a : Plane) :
    (∫ z,centeredWeight b a z*u z^6) ≤
      (54/G^2*(∫ z,transverseDensity D z)^2)*
        ∫ z,centeredWeight b a z*longitudinalDensity D z := by
  have h := radialWeight_anisotropic_H1 hG sharp pullback glue density
    (hu.translate (0,a)) hb h₀ hbound
  have hA : (∫ z,transverseDensity (fun x => D (x+(0,a))) z) =
      ∫ z,transverseDensity D z := integral_add_right_eq_self (μ := volume) (transverseDensity D) (0,a)
  have hV := centeredWeight_integral b a (fun z => u z^6)
  have hB := centeredWeight_integral b a (longitudinalDensity D)
  change (∫ z,radialWeight b z*u (z+(0,a))^6) ≤
    (54/G^2*(∫ z,transverseDensity (fun x => D (x+(0,a))) z)^2)*
      ∫ z,radialWeight b z*longitudinalDensity D (z+(0,a)) at h
  rw [hA,hV,hB] at h
  exact h

#print axioms InH1.translate
#print axioms centeredWeight_add
#print axioms centeredWeight_integral
#print axioms centeredWeight_anisotropic_H1
end BWork.Kelvin
