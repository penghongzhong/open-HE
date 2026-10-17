import FRieszL1LocalDomains
import WeakCutoffLpDomains

/-! F-only uncompiled candidate: the exact compact-cutoff domains consumed by
WeakHartreeProduct.weak_leibniz_L2_L65_H1. No weak derivative is postulated here. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.RieszL1LocalDomains
open ForcingDomain RieszConvolutionDerivative WeakCutoffLp

/-- An actual compact smooth cutoff of the literal L1-density potential has exactly
an L2 value and an L6/5 candidate weak gradient, including the cutoff error term. -/
theorem actual_riesz_cutoff_domains {α c : ℝ} {h χ : Space → ℝ}
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hh : Integrable h volume)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    MemLp (fun x => χ x * rieszConvolution α c h x) 2 volume ∧
    MemLp (fun x => χ x • gradientConvolution α c h x +
      rieszConvolution α c h x • gradient χ x)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
  classical
  let s : Set Space := tsupport χ ∪ tsupport (gradient χ)
  have hsc : IsCompact s := hχc.union (cutoff_gradient_hasCompactSupport hχc)
  have hsm : MeasurableSet s := hsc.measurableSet
  have hμs : volume s < ∞ := hsc.measure_lt_top
  let : Fact (volume s < ∞) := ⟨hμs⟩
  have hd := actual_riesz_local_domains hα2 hα3 hc hh s hμs
  have hK2 : MemLp (s.indicator (rieszConvolution α c h)) 2 volume :=
    (memLp_indicator_iff_restrict hsm.nullMeasurableSet).mpr hd.1
  have hG : MemLp (s.indicator (gradientConvolution α c h))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    (memLp_indicator_iff_restrict hsm.nullMeasurableSet).mpr hd.2
  have hK65 : MemLp (s.indicator (rieszConvolution α c h))
      (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
    (memLp_indicator_iff_restrict hsm.nullMeasurableSet).mpr
      (hd.1.mono_exponent (by norm_num))
  have hzχ (x : Space) (hx : x ∉ s) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (Or.inl ht))
  have hzGχ (x : Space) (hx : x ∉ s) : gradient χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (Or.inr ht))
  constructor
  · have hm : MemLp (fun x => χ x * s.indicator (rieszConvolution α c h) x) 2 volume :=
      (cutoff_memLp hχ.continuous hχc ∞).mul hK2
    convert hm using 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx, hzχ x]
  · have hm : MemLp (fun x => χ x • s.indicator (gradientConvolution α c h) x +
        s.indicator (rieszConvolution α c h) x • gradient χ x)
        (ENNReal.ofReal (6/5:ℝ)) volume :=
      ((cutoff_memLp hχ.continuous hχc ∞).smul hG).add
        (hK65.smul (cutoff_gradient_memLp hχ hχc ∞))
    convert hm using 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx, hzχ x, hzGχ x]

end HartreeF.RieszL1LocalDomains
