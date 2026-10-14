import DirectionalCandidateMeasurable
import FTimeFiniteNormBridge

/-! Literal HLS cross-potential bounds from finite-support pointwise data.
The sole external analytic premise is the existing all-exponents OrdinaryHLS.
The output retains the actual convolution integral domain and ENNReal norm. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain DerivativeMajorization

/-- A bounded measurable function with finite support has its actual finite Lq norm. -/
theorem finite_support_lp_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (mu : Measure X) {q M : ℝ} (hq : 0 < q) (hM : 0 ≤ M)
    {S : Set X} (hS : MeasurableSet S) (hSf : mu S ≠ ∞)
    {f : X → E} (hf : AEStronglyMeasurable f mu)
    (hbound : ∀ x, ‖f x‖ ≤ M) (hsupport : ∀ x, x ∉ S → f x = 0) :
    MemLp f (ENNReal.ofReal q) mu ∧
      eLpNorm f (ENNReal.ofReal q) mu ≤ ENNReal.ofReal M * mu S ^ (1 / q) := by
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have he : eLpNorm (S.indicator (fun _ : X => M)) (ENNReal.ofReal q) mu =
      ENNReal.ofReal M * mu S ^ (1 / q) := by
    rw [eLpNorm_indicator_const hS.nullMeasurableSet hp0 ENNReal.ofReal_ne_top,
      Real.enorm_eq_ofReal hM, ENNReal.toReal_ofReal hq.le]
  have hm : eLpNorm f (ENNReal.ofReal q) mu ≤
      eLpNorm (S.indicator (fun _ : X => M)) (ENNReal.ofReal q) mu := by
    apply eLpNorm_mono_ae hf
    filter_upwards [] with x
    by_cases hx : x ∈ S
    · simpa only [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hM] using hbound x
    · simp only [hsupport x hx, norm_zero, indicator_of_notMem hx, norm_zero, le_refl]
  rw [he] at hm
  refine ⟨hm.trans_lt (lt_top_iff_ne_top.mpr ?_), hm⟩
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hSf)

/-- The input, potential and local-factor exponent allocation, in the small-source frame. -/
theorem inner_ranges {α : ℝ} (ha : 0 < α) (ha3 : α < 3) :
    1 < 12 / (9 + α) ∧ 12 / (9 + α) < 3 / α ∧ 0 < 4 / (3 - α) ∧
    1 / (4 / (3 - α)) = 1 / (12 / (9 + α)) - α / 3 ∧
    Real.HolderTriple (4 / (3 - α)) (12 / (1 + 3 * α)) (6 / 5) := by
  have hp : 0 < 9 + α := by linarith
  have hm : 0 < 3 - α := by linarith
  refine ⟨(lt_div_iff₀ hp).2 (by linarith),
    (div_lt_div_iff₀ hp ha).2 (by nlinarith), div_pos (by norm_num) hm, ?_, ?_⟩
  · field_simp
    ring
  · constructor
    · simp only [inv_div]
      ring
    · positivity
    · positivity

/-- The allocation in the small-recipient frame. -/
theorem outer_ranges {α : ℝ} (ha : 0 < α) (ha3 : α < 3) :
    1 < 4 / (1 + α) ∧ 4 / (1 + α) < 3 / α ∧ 0 < 12 / (3 - α) ∧
    1 / (12 / (3 - α)) = 1 / (4 / (1 + α)) - α / 3 ∧
    Real.HolderTriple (12 / (3 - α)) (12 / (7 + α)) (6 / 5) := by
  have hp : 0 < 1 + α := by linarith
  have hm : 0 < 3 - α := by linarith
  refine ⟨(lt_div_iff₀ hp).2 (by linarith),
    (div_lt_div_iff₀ hp ha).2 (by nlinarith), div_pos (by norm_num) hm, ?_, ?_⟩
  · field_simp
    ring
  · constructor
    · simp only [inv_div]
      ring
    · positivity
    · positivity

/-- Actual convolution times an independent complex factor, not a scalar surrogate.
The support bounds are pointwise assumptions on the two input functions. -/
theorem convolution_product_support_bound {α c q r s : ℝ} (hH : OrdinaryHLS α c)
    (hq1 : 1 < q) (hqα : q < 3 / α) (hr : 0 < r)
    (hrel : 1 / r = 1 / q - α / 3) (hholder : Real.HolderTriple r s (6 / 5)) :
    ∃ C : ℝ≥0, ∀ (S T : Set Space), MeasurableSet S → MeasurableSet T →
      volume S ≠ ∞ → volume T ≠ ∞ →
      ∀ (A B : ℝ), 0 ≤ A → 0 ≤ B →
      ∀ (g : Space → ℝ) (f : Space → ℂ),
      AEStronglyMeasurable g volume → AEStronglyMeasurable f volume →
      (∀ x, ‖g x‖ ≤ A) → (∀ x, x ∉ S → g x = 0) →
      (∀ x, ‖f x‖ ≤ B) → (∀ x, x ∉ T → f x = 0) →
      (∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y) * g y) volume) ∧
      MemLp (fun x => rieszConvolution α c g x • f x) (ENNReal.ofReal (6/5 : ℝ)) volume ∧
      eLpNorm (fun x => rieszConvolution α c g x • f x) (ENNReal.ofReal (6/5 : ℝ)) volume ≤
        (C : ℝ≥0∞) * (ENNReal.ofReal A * volume S ^ (1/q)) *
          (ENNReal.ofReal B * volume T ^ (1/s)) := by
  obtain ⟨C,hC⟩ := hH.strong_bound q r hq1 hqα hr hrel
  refine ⟨C, fun S T hS hT hSf hTf A B hA hB g f hg hf hga hgs hfb hfs => ?_⟩
  obtain ⟨hgm,hgn⟩ := finite_support_lp_bound volume (by linarith : 0 < q) hA hS hSf hg hga hgs
  obtain ⟨hfm,hfn⟩ := finite_support_lp_bound volume hholder.symm.pos hB hT hTf hf hfb hfs
  obtain ⟨hdom,hpot,hpn⟩ := hC g hgm
  let : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal s)
      (ENNReal.ofReal (6/5 : ℝ)) := hholder.ennrealOfReal
  refine ⟨hdom,hpot.smul hfm,?_⟩
  calc
    _ ≤ eLpNorm (rieszConvolution α c g) (ENNReal.ofReal r) volume *
        eLpNorm f (ENNReal.ofReal s) volume :=
      eLpNorm_smul_le_mul_eLpNorm hpot.aestronglyMeasurable hfm.aestronglyMeasurable
    _ ≤ ((C : ℝ≥0∞) * eLpNorm g (ENNReal.ofReal q) volume) *
        (ENNReal.ofReal B * volume T ^ (1/s)) := mul_le_mul' hpn hfn
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hgn) le_rfl

#print axioms finite_support_lp_bound
#print axioms inner_ranges
#print axioms outer_ranges
#print axioms convolution_product_support_bound
end HartreeF.CompactCross
