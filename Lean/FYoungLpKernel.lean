import FSpatialLpAverage
import FEndpointSourceReflection

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.YoungSource
open ProfileSpatialSmoothing MassRecovery

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual Lp-valued convolution, with the L1 input integrated against translates of the kernel. -/
def youngValue (k : Lp ℂ p (volume : Measure Space)) (f : OneSpace) :
    Lp ℂ p (volume : Measure Space) := ∫ y : Space, f y • lpShift (-y) k

theorem young_integrable (hp : p ≠ ∞) (k : Lp ℂ p (volume : Measure Space)) (f : OneSpace) :
    Integrable (fun y : Space => f y • lpShift (-y) k) volume := by
  have hf : Integrable (f : Space → ℂ) volume := memLp_one_iff_integrable.mp (Lp.memLp f)
  apply (hf.norm.mul_const ‖k‖).mono'
    ((Lp.aestronglyMeasurable f).smul
      ((lpShift_continuous hp k).comp continuous_neg).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖f y • lpShift (-y) k‖ ≤ ‖f y‖ * ‖k‖
  rw [norm_smul, lpShift_norm]

theorem youngValue_norm (k : Lp ℂ p (volume : Measure Space)) (f : OneSpace) :
    ‖youngValue k f‖ ≤ ‖k‖ * ‖f‖ := by
  have hf : Integrable (f : Space → ℂ) volume := memLp_one_iff_integrable.mp (Lp.memLp f)
  calc
    ‖youngValue k f‖ ≤ ∫ y : Space, ‖f y‖ * ‖k‖ := by
      apply norm_integral_le_of_norm_le (hf.norm.mul_const ‖k‖)
      filter_upwards [] with y
      simp only [norm_smul, lpShift_norm, le_refl]
    _ = ‖k‖ * ‖f‖ := by rw [integral_mul_const, ← L1.norm_eq_integral_norm, mul_comm]

def youngCLM (hp : p ≠ ∞) (k : Lp ℂ p (volume : Measure Space)) :
    OneSpace →L[ℂ] Lp ℂ p (volume : Measure Space) :=
  LinearMap.mkContinuous
    { toFun := youngValue k
      map_add' := by
        intro f g
        rw [youngValue, youngValue, youngValue, ← integral_add (young_integrable hp k f) (young_integrable hp k g)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with y hy
        rw [hy]
        exact add_smul _ _ _
      map_smul' := by
        intro c f
        rw [youngValue, youngValue, ← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c f] with y hy
        rw [hy]
        change (c * f y) • lpShift (-y) k = c • (f y • lpShift (-y) k)
        exact mul_smul _ _ _ }
    ‖k‖ (youngValue_norm k)

theorem youngCLM_apply (hp : p ≠ ∞) (k : Lp ℂ p (volume : Measure Space)) (f : OneSpace) :
    youngCLM hp k f = ∫ y : Space, f y • lpShift (-y) k := rfl

theorem youngCLM_norm (hp : p ≠ ∞) (k : Lp ℂ p (volume : Measure Space)) :
    ‖youngCLM hp k‖ ≤ ‖k‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- The actual spatial operator is lifted to actual whole-line Bochner L2 sources. -/
def youngSourceCLM (hp : p ≠ ∞) (k : Lp ℂ p (volume : Measure Space)) :
    EndpointOne →L[ℂ] Lp (Lp ℂ p (volume : Measure Space)) 2 (volume : Measure ℝ) :=
  (youngCLM hp k).compLpL 2 volume

theorem youngSource_coe (hp : p ≠ ∞) (k : Lp ℂ p (volume : Measure Space)) (F : EndpointOne) :
    (youngSourceCLM hp k F : ℝ → Lp ℂ p (volume : Measure Space)) =ᵐ[volume]
      fun s => youngCLM hp k (F s) :=
  ContinuousLinearMap.coeFn_compLpL _ _

theorem youngSource_tail (hp : p ≠ ∞) (k : Lp ℂ p (volume : Measure Space))
    (F : EndpointOne) (t : ℝ) :
    tailSource t (youngSourceCLM hp k F) = youngSourceCLM hp k (tailSource t F) := by
  apply Lp.ext
  filter_upwards [tailSource_coe t (youngSourceCLM hp k F),
    youngSource_coe hp k (tailSource t F), tailSource_coe t F, youngSource_coe hp k F]
    with s h1 h2 h3 h4
  rw [h1, h2, h3]
  by_cases hs : s ∈ Set.Ici t
  · simp only [Set.indicator_of_mem hs, h4]
  · simp only [Set.indicator_of_notMem hs, map_zero]

theorem youngSource_tail_norm (hp : p ≠ ∞) (k : Lp ℂ p (volume : Measure Space))
    (F : EndpointOne) (t : ℝ) :
    tailNorm t (youngSourceCLM hp k F) ≤ ‖k‖ * tailNorm t F := by
  rw [tailNorm, youngSource_tail, tailNorm]
  exact ((youngSourceCLM hp k).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right
      ((ContinuousLinearMap.norm_compLpL_le _).trans (youngCLM_norm hp k)) (norm_nonneg _))

end HartreeF.YoungSource
