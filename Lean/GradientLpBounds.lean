import HartreeForcingDomain

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.GradientMajorants
open ForcingDomain

/-- The finite real Lp norm. The exponent argument is the usual exponent. -/
def spatialNorm (q : ℝ) (f : Space → ℝ) : ℝ :=
  (eLpNorm f (ENNReal.ofReal q) volume).toReal

/-- Actual Lp membership and a finite bound, indexed by reciprocal exponent. -/
structure SpatialBound (f : Space → ℝ) (s B : ℝ) : Prop where
  reciprocal_pos : 0 < s
  memLp : MemLp f (ENNReal.ofReal (1/s)) volume
  bound : spatialNorm (1/s) f ≤ B

theorem spatialNorm_nonneg (q : ℝ) (f : Space → ℝ) : 0 ≤ spatialNorm q f :=
  ENNReal.toReal_nonneg

theorem SpatialBound.bound_nonneg {f : Space → ℝ} {s B : ℝ}
    (h : SpatialBound f s B) : 0 ≤ B := (spatialNorm_nonneg _ _).trans h.bound

theorem spatialBound_self {q : ℝ} (hq : 0 < q) {f : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) volume) :
    SpatialBound f (1/q) (spatialNorm q f) := by
  refine ⟨by positivity, ?_, ?_⟩
  · simpa using hf
  · simp

/-- Ordinary Holder on literal real functions, with membership retained. -/
theorem SpatialBound.mul {f g : Space → ℝ} {s t A B : ℝ}
    (hf : SpatialBound f s A) (hg : SpatialBound g t B) :
    SpatialBound (fun x => f x * g x) (s+t) (A*B) := by
  have hh : Real.HolderTriple (1/s) (1/t) (1/(s+t)) := by
    constructor
    · simp only [one_div, inv_inv]
    · exact one_div_pos.mpr hf.reciprocal_pos
    · exact one_div_pos.mpr hg.reciprocal_pos
  let := hh.ennrealOfReal
  refine ⟨add_pos hf.reciprocal_pos hg.reciprocal_pos, hf.memLp.mul hg.memLp, ?_⟩
  have he : eLpNorm (fun x => f x * g x) (ENNReal.ofReal (1/(s+t))) volume ≤
      eLpNorm f (ENNReal.ofReal (1/s)) volume * eLpNorm g (ENNReal.ofReal (1/t)) volume :=
    eLpNorm_smul_le_mul_eLpNorm hf.memLp.aestronglyMeasurable hg.memLp.aestronglyMeasurable
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.memLp.eLpNorm_ne_top hg.memLp.eLpNorm_ne_top) he
  rw [ENNReal.toReal_mul] at hr
  exact hr.trans (mul_le_mul hf.bound hg.bound (spatialNorm_nonneg _ _) hf.bound_nonneg)

/-- Positive real powers of nonnegative actual functions. -/
theorem SpatialBound.rpow {f : Space → ℝ} {s B a : ℝ}
    (hf : SpatialBound f s B) (hn : ∀ x, 0 ≤ f x) (ha : 0 < a) :
    SpatialBound (fun x => f x ^ a) (a*s) (B^a) := by
  have he : (1/s)/a = 1/(a*s) := by ring_nf
  have hnorm : (fun x => ‖f x‖ ^ a) = (fun x => f x ^ a) := by
    ext x
    rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
  have hm := hf.memLp.norm_rpow_div (ENNReal.ofReal a)
  rw [ENNReal.toReal_ofReal ha.le, ← ENNReal.ofReal_div_of_pos ha, he, hnorm] at hm
  refine ⟨mul_pos ha hf.reciprocal_pos, hm, ?_⟩
  have hnrm : eLpNorm (fun x => f x ^ a) (ENNReal.ofReal (1/(a*s))) volume =
      eLpNorm f (ENNReal.ofReal (1/s)) volume ^ a := by
    rw [← he, ← hnorm, eLpNorm_norm_rpow f hf.memLp.aestronglyMeasurable ha,
      ENNReal.ofReal_div_of_pos ha,
      ENNReal.div_mul_cancel (by simpa using ha) ENNReal.ofReal_ne_top]
  unfold spatialNorm
  rw [hnrm, ← ENNReal.toReal_rpow]
  exact Real.rpow_le_rpow (spatialNorm_nonneg _ _) hf.bound ha.le

/-- Split a positive power between two actual Lp norms. -/
theorem split_power_bound {f : Space → ℝ} {a b : ℝ}
    (hn : ∀ x, 0 ≤ f x) (h6 : MemLp f 6 volume) (h10 : MemLp f 10 volume)
    (ha : 0 < a) (hb : 0 < b) :
    SpatialBound (fun x => f x ^ (a+b)) (a/6+b/10)
      (spatialNorm 6 f ^ a * spatialNorm 10 f ^ b) := by
  have hE := (spatialBound_self (q := 6) (by norm_num) (by simpa using h6)).rpow hn ha
  have hS := (spatialBound_self (q := 10) (by norm_num) (by simpa using h10)).rpow hn hb
  convert hE.mul hS using 1
  · ext x
    exact Real.rpow_add' (hn x) (by linarith : a+b ≠ 0)
  · ring_nf

/-- A single positive power assigned to the L10 factor. -/
theorem spacetime_power_bound {f : Space → ℝ} {a : ℝ}
    (hn : ∀ x, 0 ≤ f x) (h10 : MemLp f 10 volume) (ha : 0 < a) :
    SpatialBound (fun x => f x ^ a) (a/10) (spatialNorm 10 f ^ a) := by
  convert (spatialBound_self (q := 10) (by norm_num) (by simpa using h10)).rpow hn ha using 1
  ring_nf

/-- The ordinary strong HLS input range in reciprocal-exponent notation. -/
theorem reciprocal_hls_range {α s : ℝ} (hα : 0 < α)
    (hs : α/3 < s) (hs1 : s < 1) :
    1 < 1/s ∧ 1/s < 3/α ∧ 0 < 1/(s-α/3) ∧
      1/(1/(s-α/3)) = 1/(1/s)-α/3 := by
  have hs0 : 0 < s := lt_trans (by positivity) hs
  refine ⟨(lt_div_iff₀ hs0).2 (by linarith), ?_, by positivity, by simp⟩
  exact (div_lt_div_iff₀ hs0 hα).2 (by linarith)

/-- HLS for the literal Riesz convolution, preserving its actual integral domain. -/
theorem convolution_bound {α c s : ℝ} (hH : OrdinaryHLS α c)
    (hs : α/3 < s) (hs1 : s < 1) :
    ∃ C : ℝ≥0, ∀ (f : Space → ℝ) (B : ℝ), SpatialBound f s B →
      (∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y) * f y) volume) ∧
      SpatialBound (rieszConvolution α c f) (s-α/3) ((C : ℝ)*B) := by
  obtain ⟨hq1,hqα,hr,hrel⟩ := reciprocal_hls_range hH.order_pos hs hs1
  obtain ⟨C,hC⟩ := hH.strong_bound _ _ hq1 hqα hr hrel
  refine ⟨C, fun f B hf => ?_⟩
  obtain ⟨hi,hm,hb⟩ := hC f hf.memLp
  refine ⟨hi, sub_pos.mpr hs, hm, ?_⟩
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hf.memLp.eLpNorm_ne_top) hb
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hf.bound C.coe_nonneg)

/-- Enlarge a finite bound without changing the actual function or domain. -/
theorem SpatialBound.mono {f : Space → ℝ} {s A B : ℝ}
    (hf : SpatialBound f s A) (hAB : A ≤ B) : SpatialBound f s B :=
  ⟨hf.reciprocal_pos, hf.memLp, hf.bound.trans hAB⟩

/-- The ordinary Lp triangle inequality, with finite real norms. -/
theorem SpatialBound.add {f g : Space → ℝ} {s A B : ℝ}
    (hf : SpatialBound f s A) (hg : SpatialBound g s B) (hs : s ≤ 1) :
    SpatialBound (fun x => f x + g x) s (A+B) := by
  have hq : 1 ≤ ENNReal.ofReal (1/s) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hf.reciprocal_pos).2 (by linarith))
  refine ⟨hf.reciprocal_pos, hf.memLp.add hg.memLp, ?_⟩
  have he : eLpNorm (fun x => f x + g x) (ENNReal.ofReal (1/s)) volume ≤
      eLpNorm f (ENNReal.ofReal (1/s)) volume + eLpNorm g (ENNReal.ofReal (1/s)) volume :=
    eLpNorm_add_le hq
  have ht := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hf.memLp.eLpNorm_ne_top, hg.memLp.eLpNorm_ne_top⟩) he
  rw [ENNReal.toReal_add hf.memLp.eLpNorm_ne_top hg.memLp.eLpNorm_ne_top] at ht
  exact ht.trans (add_le_add hf.bound hg.bound)

/-- Explicit output exponent and finite real norm for the critical spatial bound. -/
theorem SpatialBound.critical_result {f : Space → ℝ} {B : ℝ}
    (hf : SpatialBound f (5/6) B) :
    MemLp f (ENNReal.ofReal (6/5 : ℝ)) volume ∧ spatialNorm (6/5) f ≤ B := by
  constructor
  · convert hf.memLp using 1
    norm_num
  · convert hf.bound using 1
    norm_num

end HartreeF.GradientMajorants
