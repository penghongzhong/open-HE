import FActualRieszL1WeakDerivative
import WeakLeibnizH1Factor
import FBoundedLocalFactorL6H1
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! STATIC-ONLY, UNCOMPILED CANDIDATE.
A genuine weak product equation for the literal L1-density Riesz potential.
Only a compact cutoff of the potential is put in global L2/L6/5. The cutoff
is exactly one on a neighborhood of each compact set, so its derivative
vanishes there. The full product is only asserted locally integrable.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace HartreeF.ActualUpperProduct
open SobolevStretch StationarySelfTest WeakHartreeProduct RieszL1LocalDomains
  ForcingDomain RieszConvolutionDerivative WeakHartreeChain

/-- The exact field for the actual scalar-potential/local-factor product.
Its kernel term uses the literal gradientConvolution of the SAME signed h. -/
def actualRieszLocalFactorGradient (α c : ℝ) (A : ℂ →L[ℝ] ℝ)
    (h : Space → ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  fun x => projectedLocalFactor (1 + α) A (u x) • gradientConvolution α c h x +
    rieszConvolution α c h x • projectedLocalFactorGradient (1 + α) A u U V x

theorem actualRieszLocalFactorGradient_re_formula (α c : ℝ)
    (h : Space → ℝ) (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    actualRieszLocalFactorGradient α c Complex.reCLM h u U V x =
      (ForcingDomain.localFactor α u x).re • gradientConvolution α c h x +
        rieszConvolution α c h x • localFactorGradientRe (1 + α) u U V x := by
  unfold actualRieszLocalFactorGradient
  rw [projectedLocalFactorGradient_re]
  rfl

theorem actualRieszLocalFactorGradient_im_formula (α c : ℝ)
    (h : Space → ℝ) (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    actualRieszLocalFactorGradient α c Complex.imCLM h u U V x =
      (ForcingDomain.localFactor α u x).im • gradientConvolution α c h x +
        rieszConvolution α c h x • localFactorGradientIm (1 + α) u U V x := by
  unfold actualRieszLocalFactorGradient
  rw [projectedLocalFactorGradient_im]
  rfl

/-- An actual smooth compact cutoff with a literal zero gradient on a compact set. -/
theorem compact_cutoff_plateau (k : Set Space) (hk : IsCompact k) :
    ∃ χ : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ k, χ x = 1 ∧ gradient χ x = 0 := by
  obtain ⟨r, hr, hkr⟩ := hk.isBounded.subset_ball_lt 0 (0 : Space)
  let χ : ContDiffBump (0 : Space) := ⟨r, r + 1, hr, by linarith⟩
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_⟩
  intro x hx
  have hnear : (χ : Space → ℝ) =ᶠ[𝓝 x] (1 : Space → ℝ) :=
    χ.eventuallyEq_one_of_mem_ball (hkr hx)
  refine ⟨hnear.eq_of_nhds, ?_⟩
  simpa only [Pi.one_def, gradient_fun_const] using hnear.gradient_eq

/-- The literal upper-order Riesz potential times an actual L6/H1 factor.
Its product equation is derived from compact localization and asymmetric
Leibniz. Neither this equation nor global L1 of the function is an input. -/
theorem actual_riesz_L1_product_hasWeakGradient
    (hDensity : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c)
    {h b : Space → ℝ} {B : Space → Space} (hh : Integrable h volume)
    (hwb : HasWeakGradient b B) (hb : MemLp b 6 volume) (hB : MemLp B 2 volume) :
    HasWeakGradient (fun x => rieszConvolution α c h x * b x)
      (fun x => b x • gradientConvolution α c h x + rieszConvolution α c h x • B x) := by
  classical
  have hcut (χ : Space → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
      (hχc : HasCompactSupport χ) :
      HasWeakGradient (fun x => (χ x * rieszConvolution α c h x) * b x)
        (fun x => b x • (χ x • gradientConvolution α c h x +
          rieszConvolution α c h x • gradient χ x) +
          (χ x * rieszConvolution α c h x) • B x) := by
    obtain ⟨hw, hp, hg⟩ := actual_riesz_cutoff_weak_domains hα2 hα3 hc hh hχ hχc
    exact weak_leibniz_L2_L65_H1 hDensity hSob hw hwb hp hg hb hB
  have hlocal (k : Set Space) (hk : IsCompact k) :
      ∃ f : Space → ℝ, ∃ G : Space → Space,
        HasWeakGradient f G ∧
        EqOn f (fun x => rieszConvolution α c h x * b x) k ∧
        EqOn G (fun x => b x • gradientConvolution α c h x +
          rieszConvolution α c h x • B x) k := by
    obtain ⟨χ, hχ, hχc, hχk⟩ := compact_cutoff_plateau k hk
    refine ⟨_, _, hcut χ hχ hχc, ?_, ?_⟩
    · intro x hx
      simp only [(hχk x hx).1, one_mul]
    · intro x hx
      simp only [(hχk x hx).1, (hχk x hx).2, one_smul, smul_zero, add_zero, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · apply locallyIntegrable_iff.mpr
    intro k hk
    obtain ⟨f, G, hw, hf, hG⟩ := hlocal k hk
    exact (hw.function_local.integrableOn_isCompact hk).congr_fun hf hk.measurableSet
  · apply locallyIntegrable_iff.mpr
    intro k hk
    obtain ⟨f, G, hw, hf, hG⟩ := hlocal k hk
    exact (hw.gradient_local.integrableOn_isCompact hk).congr_fun hG hk.measurableSet
  · intro v φ hφ hφc
    obtain ⟨f, G, hw, hf, hG⟩ := hlocal (tsupport φ) hφc
    calc
      _ = ∫ x, f x * fderiv ℝ φ x v := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ tsupport φ
        · rw [hf hx]
        · rw [fderiv_of_notMem_tsupport ℝ hx]
          simp only [zero_apply, mul_zero]
      _ = -(∫ x, ⟪G x, v⟫ * φ x) := hw.integration_by_parts v φ hφ hφc
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ tsupport φ
        · rw [hG hx]
        · rw [image_eq_zero_of_notMem_tsupport hx]
          simp only [mul_zero]

/-- Genuine projected product gradient for B(u)=|u|^(1+alpha)u.
The same actual u,U,V occur in the weak chain rule, bounded-domain upgrade,
and final derivative. The density remains the same arbitrary signed L1 h. -/
theorem actual_riesz_projectedLocalFactor_hasWeakGradient
    (hDensity : OrdinaryH1Density) {K α c M : ℝ} (hSob : OrdinarySobolev K)
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hM : 0 ≤ M)
    (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1)
    {h : Space → ℝ} (hh : Integrable h volume)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hb : ∀ᵐ x ∂volume, ‖u x‖ ≤ M) :
    HasWeakGradient
      (fun x => rieszConvolution α c h x * projectedLocalFactor (1 + α) A (u x))
      (actualRieszLocalFactorGradient α c A h u U V) := by
  obtain ⟨hwb, hb6, hB2⟩ := bounded_projectedLocalFactor_weak_domains hDensity
    (by linarith : 1 < 1 + α) (by linarith : 1 + α < 4) hM A hA hu hu10 hU hV hb
  exact actual_riesz_L1_product_hasWeakGradient hDensity hSob hα2 hα3 hc hh hwb hb6 hB2

#print axioms compact_cutoff_plateau
#print axioms actual_riesz_L1_product_hasWeakGradient
#print axioms actual_riesz_projectedLocalFactor_hasWeakGradient
end HartreeF.ActualUpperProduct
