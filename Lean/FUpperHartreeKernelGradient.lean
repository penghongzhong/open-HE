import FBoundedHartreeGradientMajorant
import FRieszConvolutionDerivativeEndpoint
import FWeakGradientUniqueness

/-!
UNCOMPILED DRAFT. The Riesz convolution provider was author-PASS / independent
review pending at the time of this draft. No acceptance is asserted here.

For 1 < alpha < 3 the derivative falls on the actual Riesz kernel. The same
old potential gradient is identified by uniqueness of locally integrable
weak gradients. The finite bound uses only ordinary lower-order HLS and the
existing SpatialBound calculus. The normalization ratio remains explicit.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.BoundedHartreeGradient
open ForcingDomain GradientMajorants RieszWeakDerivative WeakHartreeChain
  WeakHartreeProduct SobolevStretch StationarySelfTest RieszConvolutionDerivative

/-- Same density, same potential, and the previously defined gradient field. -/
theorem hartreePotentialGradient_eq_gradientConvolution_upperOrder
    (hDensity : OrdinaryH1Density) {α c c' : ℝ}
    (hH : OrdinaryHLS α c) (hL : OrdinaryHLS (α - 1) c')
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30 / 13 : ℝ)) volume) :
    hartreePotentialGradient α c u U V =ᵐ[volume]
      gradientConvolution α c (fun y => ‖u y‖ ^ (3 + α)) := by
  obtain ⟨C, hC⟩ := rieszConvolution_derivative_endpoint hH hL
  have hf := spatialBound_power_six (fun x => norm_nonneg (u x))
    hu.function_L6.norm (show 0 < 3 + α by linarith [hH.order_pos])
  have hm : MemLp (fun y => ‖u y‖ ^ (3 + α))
      (ENNReal.ofReal (6 / (3 + α))) volume := by
    simpa using hf.memLp
  have hw := (hC _ hm).2.2.2
  apply weakGradient_unique (hartree_potential_hasWeakGradient hDensity hH hu hu10 hU hV)
  rw [potential_eq_convolution]
  convert hw using 1
  rfl

/-- The literal lower-order scalar majorant for the differentiated potential
term, with precisely c * (3-alpha) / cprime. -/
def upperKernelMajorant (α c c' : ℝ) (W : Space → ℝ) (x : Space) : ℝ :=
  (c * (3 - α) / c') *
    rieszConvolution (α - 1) c' (fun y => W y ^ (3 + α)) x * W x ^ (2 + α)

/-- One bounded value factor and the remaining factors in L6 give L1.
No derivative norm occurs in this term. The actual convolution domain is
retained alongside the finite real bound. -/
theorem upperKernelMajorant_domain_bound {α c c' : ℝ}
    (hH : OrdinaryHLS α c) (hL : OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ≥0, ∀ (W : Space → ℝ) (M : ℝ), (∀ x, 0 ≤ W x) →
      MemLp W 6 volume → 0 ≤ M → (∀ᵐ x ∂volume, ‖W x‖ ≤ M) →
      RieszDomain (α - 1) c' (fun y => W y ^ (3 + α)) ∧
      SpatialBound (upperKernelMajorant α c c' W) 1
        (((c * (3 - α) / c') * (C : ℝ)) * M * spatialNorm 6 W ^ (4 + 2 * α)) := by
  have hα := hH.order_pos
  have hα3 := hH.order_lt_three
  have hA : 0 ≤ c * (3 - α) / c' :=
    div_nonneg (mul_nonneg hH.normalization_pos.le (by linarith)) hL.normalization_pos.le
  obtain ⟨C, hC⟩ := convolution_bound hL (s := (3 + α) / 6)
    (by linarith) (by linarith)
  refine ⟨C, fun W M hn h6 hM hWM => ?_⟩
  obtain ⟨hd, hp⟩ := hC _ _
    (spatialBound_power_six hn h6 (show 0 < 3 + α by linarith))
  have ho := spatialBound_power_six hn h6 (show 0 < 1 + α by linarith)
  have hb := spatialBound_mul_bounded (hp.mul ho) h6.aestronglyMeasurable hM hWM
  have hs := spatialBound_const_mul hb hA
  refine ⟨hd, ?_⟩
  convert hs using 1
  · funext x
    dsimp [upperKernelMajorant]
    rw [show 2 + α = 1 + (1 + α) by ring,
      Real.rpow_add' (hn x) (show 1 + (1 + α) ≠ 0 by linarith), Real.rpow_one]
    ring
  · ring
  · have hE := spatialNorm_nonneg 6 W
    have he : spatialNorm 6 W ^ (4 + 2 * α) =
        spatialNorm 6 W ^ (3 + α) * spatialNorm 6 W ^ (1 + α) := by
      rw [← Real.rpow_add' hE (show (3 + α) + (1 + α) ≠ 0 by linarith)]
      congr 1
      ring
    rw [he]
    ring

/-- Pointwise control of the old actual potential-gradient term follows only
after same-potential weak-gradient uniqueness has identified its a.e. value. -/
theorem fourthGradientMagnitude_le_upperKernelMajorant
    (hDensity : OrdinaryH1Density) {α c c' : ℝ}
    (hH : OrdinaryHLS α c) (hL : OrdinaryHLS (α - 1) c')
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30 / 13 : ℝ)) volume) :
    ∀ᵐ x ∂volume, fourthGradientMagnitude α c u U V x ≤
      upperKernelMajorant α c c' (fun y => ‖u y‖) x := by
  have hn : (fun y => ‖‖u y‖ ^ (3 + α)‖) = (fun y => ‖u y‖ ^ (3 + α)) := by
    funext y
    exact Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  filter_upwards [hartreePotentialGradient_eq_gradientConvolution_upperOrder
    hDensity hH hL hu hu10 hU hV] with x hx
  have hg := gradientConvolution_norm_le hH.order_lt_three hH.normalization_pos
    hL.normalization_pos (fun y => ‖u y‖ ^ (3 + α)) x
  rw [hn] at hg
  have hb := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (norm_nonneg (u x)) (2 + α))
  unfold fourthGradientMagnitude
  rw [hx]
  convert hb using 1
  dsimp [upperKernelMajorant]
  ring

#print axioms hartreePotentialGradient_eq_gradientConvolution_upperOrder
#print axioms upperKernelMajorant_domain_bound
#print axioms fourthGradientMagnitude_le_upperKernelMajorant
end HartreeF.BoundedHartreeGradient
