import L2CompositionContinuity
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace HartreeF.ModulusGradient

/-- Two real strong-L2 limits give a strong-L2 limit in the actual product space. -/
theorem strong_l2_pair_limit
    {u v : Space → ℝ} {un vn : ℕ → Space → ℝ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hun : ∀ n, MemLp (un n) 2 volume) (hvn : ∀ n, MemLp (vn n) 2 volume)
    (hulim : Tendsto (fun n => eLpNorm (un n - u) 2 volume) atTop (𝓝 0))
    (hvlim : Tendsto (fun n => eLpNorm (vn n - v) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => (un n x, vn n x) - (u x, v x)) 2 volume)
      atTop (𝓝 0) := by
  have ha : Tendsto (fun n => eLpNorm (fun x => ‖un n x - u x‖) 2 volume)
      atTop (𝓝 0) := by
    simpa only [← Pi.sub_apply, eLpNorm_norm _ ((hun _).sub hu).aestronglyMeasurable] using hulim
  have hb : Tendsto (fun n => eLpNorm (fun x => ‖vn n x - v x‖) 2 volume)
      atTop (𝓝 0) := by
    simpa only [← Pi.sub_apply, eLpNorm_norm _ ((hvn _).sub hv).aestronglyMeasurable] using hvlim
  apply strong_l2_zero_of_norm_le (B := 1)
    (fun n => ((hun n).sub hu).aestronglyMeasurable.prodMk ((hvn n).sub hv).aestronglyMeasurable)
    (gn := fun n x => ‖un n x - u x‖ + ‖vn n x - v x‖)
  · intro n
    filter_upwards [] with x
    change max ‖un n x - u x‖ ‖vn n x - v x‖ ≤
      1 * ‖‖un n x - u x‖ + ‖vn n x - v x‖‖
    rw [one_mul, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _))
  · exact strong_l2_zero_add ha hb

/-- A classical Lipschitz function preserves strong L2 convergence. -/
theorem lipschitz_comp_strong_l2
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {Fmap : E → F} {K : ℝ≥0} (hF : LipschitzWith K Fmap)
    {u : Space → E} {un : ℕ → Space → E}
    (hu : AEStronglyMeasurable u volume)
    (hun : ∀ n, AEStronglyMeasurable (un n) volume)
    (hlim : Tendsto (fun n => eLpNorm (un n - u) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Fmap (un n x) - Fmap (u x)) 2 volume)
      atTop (𝓝 0) := by
  apply strong_l2_zero_of_norm_le
    (fun n => (hF.continuous.comp_aestronglyMeasurable (hun n)).sub
      (hF.continuous.comp_aestronglyMeasurable hu)) (gn := fun n => un n - u)
    (B := (K : ℝ))
  · intro n
    exact ae_of_all _ (fun x => hF.norm_sub_le (un n x) (u x))
  · exact hlim

#print axioms strong_l2_pair_limit
#print axioms lipschitz_comp_strong_l2
end HartreeF.ModulusGradient
