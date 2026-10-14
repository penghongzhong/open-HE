import DirectionalCandidateMeasurable
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
namespace HartreeF.DerivativeMajorization
open GradientMajorants

theorem dominated_critical_norm {f : Space → ℂ} {g : Space → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hg : MemLp g (ENNReal.ofReal (6/5 : ℝ)) volume)
    (hC : 0≤C) (hgn : ∀ x, 0≤g x)
    (hb : ∀ᵐ x ∂volume, ‖f x‖≤C*g x) :
    MemLp f (ENNReal.ofReal (6/5 : ℝ)) volume ∧
    (eLpNorm f (ENNReal.ofReal (6/5 : ℝ)) volume).toReal≤C*spatialNorm (6/5) g := by
  have hCg := hg.const_mul C
  have ht : ∀ᵐ x ∂volume, ‖f x‖≤‖C*g x‖ := by
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC (hgn x))] using hx
  have hm := hCg.of_le hf ht
  have hnorm := eLpNorm_mono_ae (p := ENNReal.ofReal (6/5 : ℝ)) hf ht
  have hreal := ENNReal.toReal_mono hCg.eLpNorm_lt_top.ne hnorm
  have he : eLpNorm (fun x => C*g x) (ENNReal.ofReal (6/5 : ℝ)) volume=
      ENNReal.ofReal C*eLpNorm g (ENNReal.ofReal (6/5 : ℝ)) volume := by
    change eLpNorm (C • g) (ENNReal.ofReal (6/5 : ℝ)) volume=_
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hC]
  rw [he,ENNReal.toReal_mul,ENNReal.toReal_ofReal hC] at hreal
  exact ⟨hm,hreal⟩

#print axioms dominated_critical_norm
end HartreeF.DerivativeMajorization
