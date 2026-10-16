import FBoundedHartreeMajorants
import HartreeForcingWeakGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient
open ForcingDomain GradientMajorants RieszWeakDerivative WeakHartreeChain WeakHartreeProduct

theorem potential_nonneg_of_normalization {α c : ℝ} (hc : 0 ≤ c)
    (u : Space → ℂ) (x : Space) : 0 ≤ potential α c u x := by
  apply integral_nonneg
  intro y
  exact mul_nonneg (rieszKernel_nonneg hc _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem hartreeDensityGradient_norm_sharp {α : ℝ} (hα : 0 < α)
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    ‖hartreeDensityGradient α u U V x‖ ≤
      (3 + α) * (‖u x‖ ^ (2 + α) * (‖U x‖ + ‖V x‖)) := by
  rw [hartreeDensityGradient_eq]
  have h := densityGradient_norm_bound (p := 3 + α) (by linarith) u U V x
  simpa only [show 3 + α - 1 = 2 + α by ring] using h

/-- Monotonicity is applied only after an actual absolute-integrability domain
has been supplied for the scalar majorant convolution. -/
theorem hartreePotentialGradient_norm_majorant {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (u : Space → ℂ) (U V : Space → Space)
    (hd : RieszDomain α c (fun y => ‖u y‖ ^ (2 + α) * (‖U y‖ + ‖V y‖))) :
    ∀ᵐ x ∂volume, ‖hartreePotentialGradient α c u U V x‖ ≤
      (3 + α) * rieszConvolution α c (fun y => ‖u y‖ ^ (2 + α) * (‖U y‖ + ‖V y‖)) x := by
  filter_upwards [hd] with x hx
  calc
    _ ≤ rieszConvolution α c (fun y => ‖hartreeDensityGradient α u U V y‖) x :=
      rieszVectorConvolution_norm_le hc _ _
    _ ≤ ∫ y, (3 + α) * (rieszKernel α c (x - y) *
        (‖u y‖ ^ (2 + α) * (‖U y‖ + ‖V y‖))) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun y => mul_nonneg (rieszKernel_nonneg hc _) (norm_nonneg _))
        (hx.const_mul (3 + α))
      filter_upwards [] with y
      have h := mul_le_mul_of_nonneg_left (hartreeDensityGradient_norm_sharp hα u U V y)
        (rieszKernel_nonneg (α := α) hc (x - y))
      convert h using 1; ring
    _ = _ := integral_const_mul _ _

theorem firstGradientMagnitude_eq_majorant {α c : ℝ} (hc : 0 ≤ c)
    (u : Space → ℂ) (U V : Space → Space) :
    firstGradientMagnitude α c u U V =
      majorant1 α c (fun x => ‖u x‖) (fun x => ‖U x‖ + ‖V x‖) := by
  funext x
  rw [firstGradientMagnitude, Real.norm_eq_abs,
    abs_of_nonneg (potential_nonneg_of_normalization hc u x)]
  rfl

/-- The actual projected forcing gradient is dominated by the two literal L1 majorants. -/
theorem projected_forcing_gradient_majorant {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1) (u : Space → ℂ) (U V : Space → Space)
    (hd : RieszDomain α c (fun y => ‖u y‖ ^ (2 + α) * (‖U y‖ + ‖V y‖))) :
    ∀ᵐ x ∂volume,
      ‖potentialProductGradient α c (projectedLocalFactor (1 + α) A) u U V x‖ ≤
      (3 + α) * majorant4 α c (fun y => ‖u y‖) (fun y => ‖U y‖ + ‖V y‖) x +
      (3 * (2 + α)) * majorant1 α c (fun y => ‖u y‖) (fun y => ‖U y‖ + ‖V y‖) x := by
  have hb := localFactor_growth_bounds hα A hA
  filter_upwards [hartreePotentialGradient_norm_majorant hα hc u U V hd] with x hx
  have hbase := potentialProductGradient_norm_bound (c := c) hb.1 hb.2 u U V x
  apply hbase.trans
  unfold gradientMagnitude
  rw [firstGradientMagnitude_eq_majorant hc]
  refine add_le_add ?_ le_rfl
  have h := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (norm_nonneg (u x)) (2 + α))
  change ‖u x‖ ^ (2 + α) * ‖hartreePotentialGradient α c u U V x‖ ≤ _
  convert h using 1
  dsimp [majorant4]
  ring

/-- Transfer of a genuine scalar L1 majorant to a measurable actual vector field. -/
theorem memLp_one_bound_of_majorant {E : Type*} [NormedAddCommGroup E]
    {g : Space → E} {f : Space → ℝ} {B : ℝ} (hf : SpatialBound f 1 B)
    (hg : AEStronglyMeasurable g volume) (hgf : ∀ᵐ x ∂volume, ‖g x‖ ≤ f x) :
    MemLp g 1 volume ∧ (eLpNorm g 1 volume).toReal ≤ B := by
  have hf1 : MemLp f 1 volume := by simpa using hf.memLp
  have hm : MemLp g 1 volume := hf1.of_le hg (hgf.mono fun _ h => h.trans (le_abs_self _))
  refine ⟨hm, ?_⟩
  have hn := ENNReal.toReal_mono hf1.eLpNorm_ne_top (eLpNorm_mono_ae_real (p := 1) hg hgf)
  exact hn.trans (by simpa [spatialNorm] using hf.bound)

end HartreeF.BoundedHartreeGradient
