import FOrthogonalityPowerCutoff

/-! Physical-scale spelling of the conditional scalar orthogonality assembly.
The three norm bounds remain explicit inputs; this is not an analytic estimate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Filter
open scoped Topology ENNReal NNReal
namespace HartreeF.OrthogonalityCutoff

/-- Scalar assembly written with two positive physical scales. The inputs `X,T`
may subsequently be instantiated with normalized spatial and temporal separation. -/
theorem tendsto_zero_of_scales_spatial_temporal {ι : Type*} {l : Filter ι}
    {N : ι → ℝ≥0∞} {lam1 lam2 X T : ι → ℝ}
    (hlam1 : ∀ i, 0 < lam1 i) (hlam2 : ∀ i, 0 < lam2 i)
    (Cs Cx : ℝ≥0) {δ γ K L : ℝ}
    (hδ : 0 < δ) (hγ : 0 < γ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (horth : Tendsto (fun i => lam1 i/lam2 i + lam2 i/lam1 i + X i + T i) l atTop)
    (hscale : ∀ i, N i ≤ (Cs : ℝ≥0∞) *
      ENNReal.ofReal ((min (lam1 i/lam2 i) (lam2 i/lam1 i))^δ))
    (hspace : ∀ i, K * (lam1 i/lam2 i + lam2 i/lam1 i + 2) < X i →
      N i ≤ (Cx : ℝ≥0∞) * ENNReal.ofReal ((X i)^(-γ)))
    (htime : ∀ i, L * (lam1 i/lam2 i + lam2 i/lam1 i) < T i → N i = 0) :
    Tendsto N l (𝓝 0) := by
  apply tendsto_zero_of_ratio_spatial_temporal
    (r := fun i => lam1 i/lam2 i) (X := X) (T := T)
    (fun i => div_pos (hlam1 i) (hlam2 i)) Cs Cx hδ hγ hK hL
  · simpa only [inv_div] using horth
  · simpa only [inv_div] using hscale
  · simpa only [inv_div] using hspace
  · simpa only [inv_div] using htime

/-- The Hartree exponents are strictly decaying when `α<3`. This remains only
an assembly implication: the actual analytic scale/spatial/time bounds are required. -/
theorem tendsto_zero_of_hartree_bounds {ι : Type*} {l : Filter ι}
    {N : ι → ℝ≥0∞} {r X T : ι → ℝ} (hr : ∀ i, 0 < r i)
    (Cs Cx : ℝ≥0) {α K L : ℝ}
    (hα : α < 3) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (horth : Tendsto (fun i => r i + (r i)⁻¹ + X i + T i) l atTop)
    (hscale : ∀ i, N i ≤ (Cs : ℝ≥0∞) *
      ENNReal.ofReal ((min (r i) (r i)⁻¹)^((3-α)/4)))
    (hspace : ∀ i, K * (r i + (r i)⁻¹ + 2) < X i →
      N i ≤ (Cx : ℝ≥0∞) * ENNReal.ofReal ((X i)^(-(3-α)/2)))
    (htime : ∀ i, L * (r i + (r i)⁻¹) < T i → N i = 0) :
    Tendsto N l (𝓝 0) := by
  apply tendsto_zero_of_ratio_spatial_temporal hr Cs Cx
    (by linarith : 0 < (3-α)/4) (by linarith : 0 < (3-α)/2) hK hL horth hscale
  · simpa only [neg_div] using hspace
  · exact htime

#print axioms tendsto_zero_of_scales_spatial_temporal
#print axioms tendsto_zero_of_hartree_bounds
end HartreeF.OrthogonalityCutoff
