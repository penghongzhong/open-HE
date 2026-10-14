import RieszPointwiseDomination
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
namespace HartreeF.DerivativeMajorization
open ForcingDomain

theorem riesz_two_envelope_domain {α c C D : ℝ} (hc : 0≤c) (x : Space)
    {f B H : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (hB : Integrable (fun y => rieszKernel α c (x-y)*B y) volume)
    (hH : Integrable (fun y => rieszKernel α c (x-y)*H y) volume)
    (hb : ∀ y, ‖f y‖ ≤ C*B y+D*H y) :
    Integrable (fun y => rieszKernel α c (x-y)*f y) volume ∧
    ‖rieszConvolution α c f x‖ ≤ C*rieszConvolution α c B x+D*rieszConvolution α c H x := by
  have he (y : Space) : rieszKernel α c (x-y)*(C*B y+D*H y)=
      C*(rieszKernel α c (x-y)*B y)+D*(rieszKernel α c (x-y)*H y) := by ring
  have hi : Integrable (fun y => rieszKernel α c (x-y)*(C*B y+D*H y)) volume := by
    simp_rw [he]
    exact (hB.const_mul C).add (hH.const_mul D)
  obtain ⟨hd,hn⟩ := riesz_fibre_norm_domination hc x hf hi hb
  refine ⟨hd,?_⟩
  have ht : rieszConvolution α c (fun y => C*B y+D*H y) x=
      C*rieszConvolution α c B x+D*rieszConvolution α c H x := by
    unfold rieszConvolution
    simp_rw [he]
    rw [integral_add (hB.const_mul C) (hH.const_mul D),integral_const_mul,integral_const_mul]
  exact hn.trans_eq ht

theorem riesz_subtraction_of_domains {α c : ℝ} (x : Space) {f g : Space → ℝ}
    (hf : Integrable (fun y => rieszKernel α c (x-y)*f y) volume)
    (hg : Integrable (fun y => rieszKernel α c (x-y)*g y) volume) :
    rieszConvolution α c (f-g) x=rieszConvolution α c f x-rieszConvolution α c g x := by
  unfold rieszConvolution
  simp only [Pi.sub_apply,mul_sub]
  exact integral_sub hf hg

#print axioms riesz_two_envelope_domain
#print axioms riesz_subtraction_of_domains
end HartreeF.DerivativeMajorization
