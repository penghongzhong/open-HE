import CutoffGeometry
import CutoffL3Scaling

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.CutoffApproximation

/-- The exact critical L3 norm is independent of the cutoff radius. -/
theorem cutoff_gradient_eLpNorm (n : ℕ) :
    eLpNorm (gradient (cutoff n)) 3 volume =
      eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume := by
  have hf : gradient (cutoff n) = fun x =>
      cutoffScale n • gradient (baseBump : Space → ℝ) (cutoffScale n • x) :=
    funext (cutoff_gradient_formula n)
  rw [hf]
  exact eLpNorm_scale_critical_three
    (WeakCutoffLp.cutoff_gradient_continuous
      (baseBump.contDiff : ContDiff ℝ (⊤ : ℕ∞) (baseBump : Space → ℝ))).aestronglyMeasurable
    (cutoffScale_pos n)

/-- The common gradient bound is finite, produced from the fixed smooth bump. -/
theorem cutoff_gradient_eLpNorm_lt_top :
    eLpNorm (gradient (baseBump : Space → ℝ)) 3 volume < ∞ :=
  (WeakCutoffLp.cutoff_gradient_memLp
    (baseBump.contDiff : ContDiff ℝ (⊤ : ℕ∞) (baseBump : Space → ℝ))
    baseBump.hasCompactSupport 3).eLpNorm_lt_top

#print axioms cutoff_gradient_eLpNorm
#print axioms cutoff_gradient_eLpNorm_lt_top
end HartreeF.CutoffApproximation
