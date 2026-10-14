import FProfileSmoothingSequence

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation

/-- The mixed norm triangle for two successive actual approximation errors. -/
theorem mixed_sub_triangle {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hqTop : q ≠ ∞)
    (f g h : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume))
    (hh : AEStronglyMeasurable (fun z : ℝ × Space => h z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (fun t x => f t x - h t x) ≤
      mixedNorm volume volume p q (fun t x => f t x - g t x) +
      mixedNorm volume volume p q (fun t x => g t x - h t x) := by
  have hsum : (fun t x => f t x - h t x) =
      (fun t x => (f t x - g t x) + (g t x - h t x)) := by
    funext t x
    abel
  rw [hsum]
  exact mixed_add_le hp hq hqTop _ _ (hf.sub hg) (hg.sub hh)

/-- A radius-dependent common precision combined with a vanishing cutoff error gives convergence. -/
theorem tendsto_zero_of_le_precision_add {a b : ℕ → ℝ≥0∞}
    (hb : Tendsto b atTop (𝓝 0)) (hab : ∀ n, a n ≤ smoothingPrecision n + b n) :
    Tendsto a atTop (𝓝 0) := by
  have ht := smoothingPrecision_tendsto.add hb
  simp only [add_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hab

#print axioms mixed_sub_triangle
#print axioms tendsto_zero_of_le_precision_add
end HartreeF.ProfileSpatialSmoothing
