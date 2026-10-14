import ComplexWeakCutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! Literal expanding compact smooth cutoffs on HartreeF.Space. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal
namespace HartreeF.CutoffApproximation

/-- A fixed genuine smooth bump with inner radius one and outer radius two. -/
def baseBump : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩

def cutoffScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

def cutoff (n : ℕ) (x : Space) : ℝ := baseBump (cutoffScale n • x)

theorem cutoffScale_pos (n : ℕ) : 0 < cutoffScale n := by
  unfold cutoffScale
  positivity

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (cutoff n) :=
  baseBump.contDiff.comp (contDiff_id.const_smul (cutoffScale n))

theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) := by
  let e : Space ≃ₜ Space := Homeomorph.smul (Units.mk0 (cutoffScale n) (cutoffScale_pos n).ne')
  exact baseBump.hasCompactSupport.comp_homeomorph e

theorem cutoff_nonneg (n : ℕ) (x : Space) : 0 ≤ cutoff n x := baseBump.nonneg

theorem cutoff_le_one (n : ℕ) (x : Space) : cutoff n x ≤ 1 := baseBump.le_one

theorem cutoff_eq_one (n : ℕ) {x : Space} (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    cutoff n x = 1 := by
  apply baseBump.one_of_mem_closedBall
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (cutoffScale_pos n)]
  change ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ 1
  exact (inv_mul_le_iff₀ (by positivity)).2 (by simpa using hx)

theorem cutoff_eq_zero (n : ℕ) {x : Space} (hx : 2 * ((n : ℝ) + 1) ≤ ‖x‖) :
    cutoff n x = 0 := by
  apply baseBump.zero_of_le_dist
  simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (cutoffScale_pos n)]
  change 2 ≤ ((n : ℝ) + 1)⁻¹ * ‖x‖
  exact (le_inv_mul_iff₀ (by positivity)).2 (by nlinarith)

theorem cutoff_eventually_one (x : Space) : ∀ᶠ n : ℕ in atTop, cutoff n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply cutoff_eq_one
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The cutoff is identically one on a neighbourhood of every point in ball n. -/
theorem cutoff_eventuallyEq_one (n : ℕ) {x : Space} (hx : ‖x‖ ≤ (n : ℝ)) :
    cutoff n =ᶠ[𝓝 x] (fun _ => 1) := by
  have hx' : x ∈ ball (0 : Space) ((n : ℝ) + 1) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  filter_upwards [isOpen_ball.mem_nhds hx'] with y hy
  exact cutoff_eq_one n (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy))

theorem cutoff_gradient_zero (n : ℕ) {x : Space} (hx : ‖x‖ ≤ (n : ℝ)) :
    gradient (cutoff n) x = 0 := by
  rw [(cutoff_eventuallyEq_one n hx).gradient_eq]
  exact gradient_fun_const x 1

/-- The chain rule for the actual Mathlib gradient under real scalar dilation. -/
theorem gradient_comp_smul {f : Space → ℝ} (hf : Differentiable ℝ f)
    (a : ℝ) (x : Space) :
    gradient (fun y => f (a • y)) x = a • gradient f (a • x) := by
  have hd := (hf (a • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul a)
  have hder : fderiv ℝ (fun y => f (a • y)) x = a • fderiv ℝ f (a • x) := by
    convert hd.fderiv using 1
    · congr 1
    · simp only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id]
  simp only [gradient, hder, map_smul]

theorem cutoff_gradient_formula (n : ℕ) (x : Space) :
    gradient (cutoff n) x = cutoffScale n • gradient (baseBump : Space → ℝ)
      (cutoffScale n • x) := by
  exact gradient_comp_smul ((baseBump.contDiff : ContDiff ℝ (⊤ : ℕ∞) (baseBump : Space → ℝ)).differentiable (by simp)) _ _

theorem cutoff_gradient_L3 (n : ℕ) : MemLp (gradient (cutoff n)) 3 volume :=
  WeakCutoffLp.cutoff_gradient_memLp (cutoff_smooth n) (cutoff_compact n) 3

theorem cutoff_L2_and_dotH1 {u : Space → ℂ} {GRe GIm : Space → Space}
    (h : SobolevStretch.InDotH1 u GRe GIm) (n : ℕ) :
    MemLp (fun x => cutoff n x • u x) 2 volume ∧
    SobolevStretch.InDotH1 (fun x => cutoff n x • u x)
      (fun x => cutoff n x • GRe x + (u x).re • gradient (cutoff n) x)
      (fun x => cutoff n x • GIm x + (u x).im • gradient (cutoff n) x) :=
  h.cutoff_L2_and_dotH1 (cutoff_smooth n) (cutoff_compact n)

#print axioms cutoffScale_pos
#print axioms cutoff_smooth
#print axioms cutoff_compact
#print axioms cutoff_nonneg
#print axioms cutoff_le_one
#print axioms cutoff_eq_one
#print axioms cutoff_eq_zero
#print axioms cutoff_eventually_one
#print axioms cutoff_eventuallyEq_one
#print axioms cutoff_gradient_zero
#print axioms gradient_comp_smul
#print axioms cutoff_gradient_formula
#print axioms cutoff_gradient_L3
#print axioms cutoff_L2_and_dotH1
end HartreeF.CutoffApproximation
