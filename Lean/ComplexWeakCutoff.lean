import WeakSmoothProduct
import WeakCutoffLpDomains

/-!
Actual localization in the C11 complex homogeneous Sobolev domain.
The input only has L6 function control and L2 real/imaginary weak gradients.
The output function is also L2, and all four terms of the product gradients
have independently produced L2 domains.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace HartreeF.SobolevStretch
open DirectionalStretch WeakCutoffLp

/-- Each summand of the two actual product gradients has an L2 domain. -/
theorem InDotH1.cutoff_gradient_term_domains {u : Space → ℂ}
    {GRe GIm : Space → Space} (h : InDotH1 u GRe GIm)
    {χ : Space → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) :
    MemLp (fun x => χ x • GRe x) 2 volume ∧
    MemLp (fun x => (u x).re • gradient χ x) 2 volume ∧
    MemLp (fun x => χ x • GIm x) 2 volume ∧
    MemLp (fun x => (u x).im • gradient χ x) 2 volume := by
  exact ⟨cutoff_gradient_field_memLp_two hχ.continuous hc h.real_gradient_L2,
    function_smul_cutoff_gradient_memLp_two hχ hc
      (h.function_L6.continuousLinearMap_comp Complex.reCLM),
    cutoff_gradient_field_memLp_two hχ.continuous hc h.imag_gradient_L2,
    function_smul_cutoff_gradient_memLp_two hχ hc
      (h.function_L6.continuousLinearMap_comp Complex.imCLM)⟩

/-- Compact smooth localization preserves actual dotH1 and produces the
literal classical-gradient correction to each real weak gradient. -/
theorem InDotH1.cutoff {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : InDotH1 u GRe GIm) {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    InDotH1 (fun x => χ x • u x)
      (fun x => χ x • GRe x + (u x).re • gradient χ x)
      (fun x => χ x • GIm x + (u x).im • gradient χ x) := by
  have ht := h.cutoff_gradient_term_domains hχ hc
  refine ⟨cutoff_smul_memLp hχ.continuous hc h.function_L6,
    ht.1.add ht.2.1, ht.2.2.1.add ht.2.2.2, ?_, ?_⟩
  · convert h.real_weak.mul_smooth hχ using 1
    funext x
    simp [Complex.real_smul]
  · convert h.imag_weak.mul_smooth hχ using 1
    funext x
    simp [Complex.real_smul]

/-- The localized function is globally L2 even when the original dotH1
function was assumed only L6. -/
theorem InDotH1.cutoff_memLp_two {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : InDotH1 u GRe GIm) {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemLp (fun x => χ x • u x) 2 volume :=
  cutoff_smul_memLp_two hχ.continuous hc h.function_L6

/-- Bundled localization endpoint: L2 together with the actual C11 dotH1
domain and explicitly identified weak gradients. -/
theorem InDotH1.cutoff_L2_and_dotH1 {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : InDotH1 u GRe GIm) {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemLp (fun x => χ x • u x) 2 volume ∧
    InDotH1 (fun x => χ x • u x)
      (fun x => χ x • GRe x + (u x).re • gradient χ x)
      (fun x => χ x • GIm x + (u x).im • gradient χ x) :=
  ⟨h.cutoff_memLp_two hχ hc, h.cutoff hχ hc⟩

#print axioms InDotH1.cutoff_gradient_term_domains
#print axioms InDotH1.cutoff
#print axioms InDotH1.cutoff_memLp_two
#print axioms InDotH1.cutoff_L2_and_dotH1
end HartreeF.SobolevStretch
