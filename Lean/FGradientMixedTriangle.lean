import FGradientSliceMeasurability
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

theorem pack_mixed_norm_le {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (F G : Fin 3 → T → Space → ℂ)
    (hG : ∀ i, AEStronglyMeasurable (fun z : T × Space => G i z.1 z.2) (mu.prod volume))
    (heq : ∀ i, ∀ᵐ t ∂mu, F i t =ᵐ[volume] G i t) :
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => packGradient (F 0 t x) (F 1 t x) (F 2 t x)) ≤
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ)) (F 0) +
      mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ)) (F 1) +
      mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ)) (F 2) := by
  let a : Fin 3 → T → ℝ≥0∞ := fun i t => eLpNorm (F i t) (ENNReal.ofReal (6/5 : ℝ)) volume
  have hm := pack_slice_norm_measurable mu F G hG heq
  have hSpace : ∀ᵐ t ∂mu, eLpNorm
      (fun x => packGradient (F 0 t x) (F 1 t x) (F 2 t x))
      (ENNReal.ofReal (6/5 : ℝ)) volume ≤ a 0 t + a 1 t + a 2 t := by
    filter_upwards [heq 0, heq 1, heq 2,
      (hG 0).prodMk_left, (hG 1).prodMk_left, (hG 2).prodMk_left] with t h0 h1 h2 hg0 hg1 hg2
    have hf0 := hg0.congr h0.symm
    have hf1 := hg1.congr h1.symm
    have hf2 := hg2.congr h2.symm
    have htri := (eLpNorm_add_le (f := (fun x => F 0 t x • EuclideanSpace.basisFun (Fin 3) ℂ 0) +
      (fun x => F 1 t x • EuclideanSpace.basisFun (Fin 3) ℂ 1))
      (g := fun x => F 2 t x • EuclideanSpace.basisFun (Fin 3) ℂ 2)
      (μ := volume) (p := ENNReal.ofReal (6/5 : ℝ)) (by norm_num)).trans
      (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl)
    change eLpNorm
      (((fun x => F 0 t x • EuclideanSpace.basisFun (Fin 3) ℂ 0) +
        (fun x => F 1 t x • EuclideanSpace.basisFun (Fin 3) ℂ 1)) +
        (fun x => F 2 t x • EuclideanSpace.basisFun (Fin 3) ℂ 2))
      (ENNReal.ofReal (6/5 : ℝ)) volume ≤
      eLpNorm (F 0 t) (ENNReal.ofReal (6/5 : ℝ)) volume +
      eLpNorm (F 1 t) (ENNReal.ofReal (6/5 : ℝ)) volume +
      eLpNorm (F 2 t) (ENNReal.ofReal (6/5 : ℝ)) volume
    simpa only [coordinate_embedding_lp volume _ _ hf0 0,
      coordinate_embedding_lp volume _ _ hf1 1, coordinate_embedding_lp volume _ _ hf2 2] using htri
  have hTime : eLpNorm (fun t => eLpNorm
      (fun x => packGradient (F 0 t x) (F 1 t x) (F 2 t x))
      (ENNReal.ofReal (6/5 : ℝ)) volume) 2 mu ≤
      eLpNorm (fun t => a 0 t + a 1 t + a 2 t) 2 mu := by
    apply eLpNorm_mono_enorm_ae hm
    simpa only [enorm_eq_self] using hSpace
  exact hTime.trans ((eLpNorm_add_le (p := 2) (by norm_num)).trans
    (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl))

theorem pack_mixed_norm_ne_top {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (F G : Fin 3 → T → Space → ℂ)
    (hG : ∀ i, AEStronglyMeasurable (fun z : T × Space => G i z.1 z.2) (mu.prod volume))
    (heq : ∀ i, ∀ᵐ t ∂mu, F i t =ᵐ[volume] G i t)
    (hFin : ∀ i, mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ)) (F i) ≠ ∞) :
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => packGradient (F 0 t x) (F 1 t x) (F 2 t x)) ≠ ∞ := by
  have hB := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hFin 0, hFin 1⟩, hFin 2⟩
  exact ne_top_of_le_ne_top hB (pack_mixed_norm_le mu F G hG heq)

end HartreeF.TimeHolder
