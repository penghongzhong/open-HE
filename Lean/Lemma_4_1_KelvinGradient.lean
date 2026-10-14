import Lemma_4_1_KelvinChangeOfVariables

/-! The actual Frechet gradient of the scalar pullback, not a free vector
substituted for a derivative. Also records the exact boundary trace matching.
This remains support for Lemma 4.1, not a full H1 extension theorem. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace BWork.Kelvin

def planarGradient (f : Plane → ℝ) (p : Plane) : Plane :=
  (fderiv ℝ f p (1,0), fderiv ℝ f p (0,1))

theorem linear_apply_plane (F : Plane →L[ℝ] ℝ) (p : Plane) :
    F p = p.1*F (1,0)+p.2*F (0,1) := by
  have he : p = p.1 • ((1,0) : Plane)+p.2 • ((0,1) : Plane) := by ext <;> simp
  conv_lhs => rw [he]
  rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]

theorem gradient_pullback {R : ℝ} {p : Plane} (hp : s p.1 p.2 ≠ 0)
    {f : Plane → ℝ} (hf : DifferentiableAt ℝ f (inversion R p)) :
    planarGradient (f ∘ inversion R) p = jacobian R p (planarGradient f (inversion R p)) := by
  have hi := derivative_inversion R p hp
  unfold planarGradient
  rw [fderiv_comp p hf hi.differentiableAt, hi.fderiv]
  simp only [ContinuousLinearMap.comp_apply, jacobian_apply]
  ext <;> simp only [mul_one,mul_zero,add_zero,zero_add]
  · exact linear_apply_plane _ _
  · exact linear_apply_plane _ _

theorem actual_transverse_energy {R : ℝ} (hR : 0 < R) {f : Plane → ℝ}
    (hf : DifferentiableOn ℝ f (exteriorDisk R)) :
    (∫ p in innerDisk R, s (planarGradient (f ∘ inversion R) p).1
        (planarGradient (f ∘ inversion R) p).2) =
      ∫ p in exteriorDisk R, s (planarGradient f p).1 (planarGradient f p).2 := by
  rw [← kelvin_transverse_energy hR (planarGradient f)]
  apply setIntegral_congr_fun (innerDisk_measurable R)
  intro p hp
  have hout : IsOpen (exteriorDisk R) := by
    have hc : Continuous (fun z : Plane => s z.1 z.2) := by unfold s; fun_prop
    exact hc.isOpen_preimage _ isOpen_Ioi
  have hd := (hf (inversion R p) (inversion_inner_mem hR hp)).differentiableAt
    (hout.mem_nhds (inversion_inner_mem hR hp))
  dsimp only
  rw [gradient_pullback hp.1.ne' hd]

theorem inversion_on_circle {R : ℝ} (hR : 0 < R) {p : Plane}
    (hp : s p.1 p.2 = R^2) : inversion R p = p := by
  have hR2 : R^2 ≠ 0 := pow_ne_zero _ hR.ne'
  ext <;> simp only [inversion,kx,ky,hp] <;> field_simp

theorem boundary_values_match {R : ℝ} (hR : 0 < R) (f : Plane → ℝ) {p : Plane}
    (hp : s p.1 p.2 = R^2) : (f ∘ inversion R) p = f p := by
  rw [Function.comp_apply,inversion_on_circle hR hp]

#print axioms gradient_pullback
#print axioms actual_transverse_energy
#print axioms boundary_values_match
end BWork.Kelvin
