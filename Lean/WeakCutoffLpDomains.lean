import WeakDirectionalStretch
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
Actual smooth compact cutoffs and their literal Mathlib gradients on the F
Euclidean space. The endpoint and Holder arguments produce all cutoff Lp domains.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set InnerProductSpace
open scoped ENNReal

namespace HartreeF.WeakCutoffLp
open DirectionalStretch

/-- Every continuous compactly supported cutoff belongs to every Lp class. -/
theorem cutoff_memLp {χ : Space → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (p : ℝ≥0∞) : MemLp χ p volume :=
  hχ.memLp_of_hasCompactSupport hc

/-- The literal Mathlib gradient of a smooth cutoff is continuous. -/
theorem cutoff_gradient_continuous {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) : Continuous (gradient χ) := by
  exact (toDual ℝ Space).symm.continuous.comp (hχ.continuous_fderiv (by simp))

/-- Compact support passes to the literal Mathlib gradient. -/
theorem cutoff_gradient_hasCompactSupport {χ : Space → ℝ}
    (hc : HasCompactSupport χ) : HasCompactSupport (gradient χ) := by
  exact (hc.fderiv ℝ).comp_left (map_zero (toDual ℝ Space).symm)

/-- The gradient of a smooth compact cutoff belongs to every Lp class. -/
theorem cutoff_gradient_memLp {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (p : ℝ≥0∞) :
    MemLp (gradient χ) p volume :=
  (cutoff_gradient_continuous hχ).memLp_of_hasCompactSupport
    (cutoff_gradient_hasCompactSupport hc)

/-- The cutoff and its gradient have the L3 and Linfinity domains needed by Holder. -/
theorem cutoff_domains {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    MemLp χ 3 volume ∧ MemLp χ ∞ volume ∧
      MemLp (gradient χ) 3 volume ∧ MemLp (gradient χ) ∞ volume := by
  exact ⟨cutoff_memLp hχ.continuous hc 3, cutoff_memLp hχ.continuous hc ∞,
    cutoff_gradient_memLp hχ hc 3, cutoff_gradient_memLp hχ hc ∞⟩

/-- Holder with exponents 3, 6, 2 for a real cutoff and any real normed module. -/
theorem cutoff_smul_memLp_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : Space → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {u : Space → E} (hu : MemLp u 6 volume) :
    MemLp (fun x => χ x • u x) 2 volume := by
  have : ENNReal.HolderTriple 3 6 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num⟩
  exact (cutoff_memLp hχ hc 3).smul hu

/-- A bounded compact cutoff preserves the input Lp exponent. -/
theorem cutoff_smul_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : Space → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {u : Space → E} {p : ℝ≥0∞} (hu : MemLp u p volume) :
    MemLp (fun x => χ x • u x) p volume := by
  exact (cutoff_memLp hχ hc ∞).smul hu

/-- A compact cutoff turns a complex L6 function into both L2 and L6. -/
theorem complex_cutoff_domains {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    {u : Space → ℂ} (hu : MemLp u 6 volume) :
    MemLp (fun x => χ x • u x) 2 volume ∧
      MemLp (fun x => χ x • u x) 6 volume :=
  ⟨cutoff_smul_memLp_two hχ.continuous hc hu, cutoff_smul_memLp hχ.continuous hc hu⟩

/-- The cutoff preserves an actual vector-valued L2 weak gradient. -/
theorem cutoff_gradient_field_memLp_two {χ : Space → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {G : Space → Space} (hG : MemLp G 2 volume) :
    MemLp (fun x => χ x • G x) 2 volume :=
  cutoff_smul_memLp hχ hc hG

/-- Holder with exponents 6, 3, 2 produces the cutoff-gradient error domain. -/
theorem function_smul_cutoff_gradient_memLp_two {χ : Space → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    {u : Space → ℝ} (hu : MemLp u 6 volume) :
    MemLp (fun x => u x • gradient χ x) 2 volume := by
  have : ENNReal.HolderTriple 6 3 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num⟩
  exact hu.smul (cutoff_gradient_memLp hχ hc 3)

#print axioms cutoff_memLp
#print axioms cutoff_gradient_continuous
#print axioms cutoff_gradient_hasCompactSupport
#print axioms cutoff_gradient_memLp
#print axioms cutoff_domains
#print axioms cutoff_smul_memLp_two
#print axioms cutoff_smul_memLp
#print axioms complex_cutoff_domains
#print axioms cutoff_gradient_field_memLp_two
#print axioms function_smul_cutoff_gradient_memLp_two
end HartreeF.WeakCutoffLp
