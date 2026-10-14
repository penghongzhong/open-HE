import CutoffEstimates
import FiniteLpTail

/-!
Actual homogeneous cutoff approximation. The input is L6 with L2 weak gradients;
no global L2 hypothesis is introduced. Cutoffs are compact but the localized weak
function need not be smooth. A subsequent H1 smoothing step is still required.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace HartreeF.CutoffApproximation

/-- Genuine finite-Lp convergence, using a finite Lp tail on all of R3. -/
theorem cutoff_eLpNorm_tendsto_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Space → E} {p : ℝ≥0∞} (hf : MemLp f p volume) (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun x => cutoff n x • f x - f x) p volume)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (exteriorTail_eLpNorm_tendsto_zero hf hp0 hpt)
  · intro n
    exact bot_le
  · exact cutoff_sub_eLpNorm_le_tail hf.aestronglyMeasurable

/-- The critical gradient correction vanishes by Holder and the actual L6 tail. -/
theorem cutoff_gradient_correction_tendsto_zero {u : Space → ℝ}
    (hu : MemLp u 6 volume) :
    Tendsto (fun n => eLpNorm (fun x => u x • gradient (cutoff n) x) 2 volume)
      atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.mul_const
    (exteriorTail_eLpNorm_tendsto_zero hu (by norm_num) (by norm_num))
    (Or.inr cutoff_gradient_eLpNorm_lt_top.ne)
  simp only [zero_mul] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact bot_le
  · exact cutoff_gradient_correction_eLpNorm_le_tail u

/-- The actual product weak gradient converges in L2. -/
theorem cutoff_full_gradient_tendsto_zero {u : Space → ℝ} {G : Space → Space}
    (hu : MemLp u 6 volume) (hG : MemLp G 2 volume) :
    Tendsto (fun n => eLpNorm
      (fun x => cutoff n x • G x + u x • gradient (cutoff n) x - G x) 2 volume)
      atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.mul_const
    (exteriorTail_eLpNorm_tendsto_zero hu (by norm_num) (by norm_num))
    (Or.inr cutoff_gradient_eLpNorm_lt_top.ne)
  simp only [zero_mul] at ht
  have hb := (exteriorTail_eLpNorm_tendsto_zero hG (by norm_num) (by norm_num)).add ht
  simp only [zero_add] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
  · intro n
    exact bot_le
  · exact cutoff_full_gradient_error_le u G hG.aestronglyMeasurable

/-- Actual complex homogeneous Sobolev localization and both strong gradient limits. -/
theorem inDotH1_cutoff_approximation {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : SobolevStretch.InDotH1 u GRe GIm) :
    (∀ n, MemLp (fun x => cutoff n x • u x) 2 volume ∧
      SobolevStretch.InDotH1 (fun x => cutoff n x • u x)
        (fun x => cutoff n x • GRe x + (u x).re • gradient (cutoff n) x)
        (fun x => cutoff n x • GIm x + (u x).im • gradient (cutoff n) x)) ∧
    Tendsto (fun n => eLpNorm (fun x => cutoff n x • u x - u x) 6 volume)
      atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => cutoff n x • GRe x + (u x).re • gradient (cutoff n) x - GRe x) 2 volume)
      atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      (fun x => cutoff n x • GIm x + (u x).im • gradient (cutoff n) x - GIm x) 2 volume)
      atTop (𝓝 0) := by
  exact ⟨cutoff_L2_and_dotH1 h,
    cutoff_eLpNorm_tendsto_zero h.function_L6 (by norm_num) (by norm_num),
    cutoff_full_gradient_tendsto_zero
      (h.function_L6.continuousLinearMap_comp Complex.reCLM) h.real_gradient_L2,
    cutoff_full_gradient_tendsto_zero
      (h.function_L6.continuousLinearMap_comp Complex.imCLM) h.imag_gradient_L2⟩

#print axioms cutoff_eLpNorm_tendsto_zero
#print axioms cutoff_gradient_correction_tendsto_zero
#print axioms cutoff_full_gradient_tendsto_zero
#print axioms inDotH1_cutoff_approximation
end HartreeF.CutoffApproximation
