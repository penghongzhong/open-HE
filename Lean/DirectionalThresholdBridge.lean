import Mathlib.Tactic

/-! Algebraic consumer for the integrated spectral tangent bound. The three
physical identifications (stretched kinetic energy, Riesz spectral energy,
and directional pressure) remain separate, visible obligations. -/
noncomputable section
set_option autoImplicit false
namespace HartreeF

theorem threshold_tangent_coercivity {p G A As D Dstretch P : ℝ}
    (hp : 0 < p) (hgap : A < G) (hAs : 0 < As)
    (hsharp : Dstretch ≤ G)
    (htangent : D + ((G-A)/As)*p*P ≤ Dstretch) :
    2*((p-1)/(2*p)*G-(A/2-D/(2*p)))*As/(G-A) ≤ As-P := by
  have hg : 0 < G-A := sub_pos.mpr hgap
  apply (div_le_iff₀ hg).mpr
  have h := htangent.trans hsharp
  have h' : (D + ((G-A)/As)*p*P)*As ≤ G*As :=
    mul_le_mul_of_nonneg_right h hAs.le
  have hid : (D + ((G-A)/As)*p*P)*As = D*As+(G-A)*p*P := by
    field_simp
  rw [hid] at h'
  have halg : 2*((p-1)/(2*p)*G-(A/2-D/(2*p)))*As =
      ((p*G-G-p*A+D)*As)/p := by field_simp; ring
  rw [halg]
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem directional_gap_positive {p G A As D Dstretch P : ℝ}
    (hp : 0 < p) (hgap : A < G) (hAs : 0 < As)
    (henergy : A/2-D/(2*p) < (p-1)/(2*p)*G)
    (hsharp : Dstretch ≤ G)
    (htangent : D + ((G-A)/As)*p*P ≤ Dstretch) : 0 < As-P := by
  have h := threshold_tangent_coercivity hp hgap hAs hsharp htangent
  have hleft : 0 < 2*((p-1)/(2*p)*G-(A/2-D/(2*p)))*As/(G-A) := by
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr henergy)) hAs
    · exact sub_pos.mpr hgap
  exact lt_of_lt_of_le hleft h

#print axioms threshold_tangent_coercivity
#print axioms directional_gap_positive
end HartreeF
