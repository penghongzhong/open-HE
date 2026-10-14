import FFiniteProfileMixedDefects
import FJointDirectionalCandidate

/-! Ordinary HLS lifted to the genuine extended mixed norm. Signed fibre
integrability and measurable time norms are established before any real norm. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteProfileRieszMixed
open TimeHolder ForcingDomain CompactCross LocalProfileProducts FiniteProfileMixedDefects

/-- One HLS constant works for every actual input field and every allowed time
exponent. Its output contains the actual absolute fibre domain as well as its norm. -/
theorem mixed_riesz_bound {α c q r : ℝ} (hH : OrdinaryHLS α c)
    (hq1 : 1 < q) (hqα : q < 3/α) (hr : 0 < r)
    (hrel : 1/r = 1/q - α/3) :
    ∃ C : ℝ≥0, ∀ (p : ℝ≥0∞), p ≠ 0 → ∀ f : ℝ → Space → ℝ,
      AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume) →
      mixedNorm volume volume p (ENNReal.ofReal q) f ≠ ∞ →
      (∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
        Integrable (fun y => rieszKernel α c (x-y) * f t y) volume) ∧
      (∀ᵐ t ∂volume, MemLp (rieszConvolution α c (f t)) (ENNReal.ofReal r) volume) ∧
      mixedNorm volume volume p (ENNReal.ofReal r)
        (fun t => rieszConvolution α c (f t)) ≤
          (C : ℝ≥0∞) * mixedNorm volume volume p (ENNReal.ofReal q) f := by
  obtain ⟨C, hC⟩ := hH.strong_bound q r hq1 hqα hr hrel
  refine ⟨C, ?_⟩
  intro p hp f hf hfin
  have hq : 0 < q := lt_trans zero_lt_one hq1
  have hq0 : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  have hr0 : ENNReal.ofReal r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hr)
  have hs := mixed_ae_slice hp f hfin
  have hF := joint_riesz_measurable volume α c f hf
  have hAll := hs.mono fun t ht => hC (f t) ht
  refine ⟨hAll.mono fun _ ht => ht.1, hAll.mono fun _ ht => ht.2.1, ?_⟩
  let A : ℝ → ℝ := fun t => (eLpNorm (f t) (ENNReal.ofReal q) volume).toReal
  have hm := spatial_lp_time_measurable volume volume (ENNReal.ofReal r)
    hr0 ENNReal.ofReal_ne_top (fun t => rieszConvolution α c (f t)) hF
  calc
    mixedNorm volume volume p (ENNReal.ofReal r)
        (fun t => rieszConvolution α c (f t)) ≤
        eLpNorm (fun t => (C : ℝ) * A t) p volume := by
      apply eLpNorm_mono_enorm_ae hm
      filter_upwards [hs] with t ht
      have hb := (hC (f t) ht).2.2
      simpa only [A, enorm_eq_self,
        Real.enorm_eq_ofReal (mul_nonneg C.coe_nonneg ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ENNReal.ofReal_toReal ht.eLpNorm_ne_top] using hb
    _ = (C : ℝ≥0∞) * mixedNorm volume volume p (ENNReal.ofReal q) f := by
      change eLpNorm ((C : ℝ) • A) p volume = _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal C.coe_nonneg,
        ENNReal.ofReal_coe_nnreal,
        real_slice_mixed_eq volume p (ENNReal.ofReal q) hq0 ENNReal.ofReal_ne_top f hf hs]

/-- Real signed coefficients multiplying complex fields, with actual domains
on both sides of the time/space Hölder estimate. -/
theorem mixed_smul_le {p₁ p₂ p q₁ q₂ q : ℝ≥0∞}
    [ENNReal.HolderTriple p₁ p₂ p] [ENNReal.HolderTriple q₁ q₂ q]
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hq₁ : q₁ ≠ 0) (hq₁T : q₁ ≠ ∞) (hq₂ : q₂ ≠ 0) (hq₂T : q₂ ≠ ∞)
    (hq : q ≠ 0) (hqT : q ≠ ∞)
    (f : ℝ → Space → ℝ) (g : ℝ → Space → ℂ)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume))
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume))
    (hff : mixedNorm volume volume p₁ q₁ f ≠ ∞)
    (hgf : mixedNorm volume volume p₂ q₂ g ≠ ∞) :
    mixedNorm volume volume p q (fun t x => f t x • g t x) ≤
      mixedNorm volume volume p₁ q₁ f * mixedNorm volume volume p₂ q₂ g := by
  apply le_trans (ProfileApproximation.mixed_mono hq hqT (hf.smul hg) ?_)
    (mixed_normProduct_le hp₁ hp₂ hq₁ hq₁T hq₂ hq₂T hq hqT f g hf hg hff hgf)
  intro t x
  simp only [norm_smul, normProduct,
    Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), le_refl]

/-- A real Riesz coefficient paired with a complex local factor in N. -/
theorem riesz_product_estimate {α c q r v : ℝ} (hH : OrdinaryHLS α c)
    (hq1 : 1 < q) (hqα : q < 3/α) (hr : 0 < r) (hv : 0 < v)
    (hrel : 1/r = 1/q - α/3)
    {p₁ p₂ : ℝ≥0∞} [ENNReal.HolderTriple p₁ p₂ 2]
    [ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal v) (ENNReal.ofReal (6/5 : ℝ))]
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0) :
    ∃ C : ℝ≥0, ∀ (f : ℝ → Space → ℝ) (g : ℝ → Space → ℂ),
      AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume) →
      AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) (volume.prod volume) →
      mixedNorm volume volume p₁ (ENNReal.ofReal q) f ≠ ∞ →
      mixedNorm volume volume p₂ (ENNReal.ofReal v) g ≠ ∞ →
      forcingNorm (fun t x => rieszConvolution α c (f t) x • g t x) ≠ ∞ ∧
      forcingNorm (fun t x => rieszConvolution α c (f t) x • g t x) ≤
        (C : ℝ≥0∞) * mixedNorm volume volume p₁ (ENNReal.ofReal q) f *
          mixedNorm volume volume p₂ (ENNReal.ofReal v) g := by
  obtain ⟨C, hC⟩ := mixed_riesz_bound hH hq1 hqα hr hrel
  refine ⟨C, ?_⟩
  intro f g hf hg hff hgf
  have hR := (hC p₁ hp₁ f hf hff).2.2
  have hRf : mixedNorm volume volume p₁ (ENNReal.ofReal r)
      (fun t => rieszConvolution α c (f t)) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hff) hR
  have hb := (mixed_smul_le (p := 2) hp₁ hp₂
    (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.ofReal_pos.mpr hv)) ENNReal.ofReal_ne_top
    (by norm_num : ENNReal.ofReal (6/5 : ℝ) ≠ 0) ENNReal.ofReal_ne_top
    (fun t => rieszConvolution α c (f t)) g
    (joint_riesz_measurable volume α c f hf) hg hRf hgf).trans
      (mul_le_mul' hR le_rfl)
  exact ⟨ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hff) hgf) hb, hb⟩

private theorem vanish_of_bound {κ : Type*} {l : Filter κ}
    {a b : κ → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (ha : Tendsto a l (𝓝 0)) (hb : ∀ n, b n ≤ C * a n) :
    Tendsto b l (𝓝 0) := by
  have ht : Tendsto (fun n => C * a n) l (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.rpow_one] using
      (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC (by norm_num : (0 : ℝ) < 1)).comp ha
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb

/-- Either slot may be the small one. The bounded companion is finite uniformly
on the original index/filter, never by a posteriori convergence of the product. -/
theorem riesz_product_tendsto {κ : Type*} {l : Filter κ}
    {α c q r v : ℝ} (hH : OrdinaryHLS α c)
    (hq1 : 1 < q) (hqα : q < 3/α) (hr : 0 < r) (hv : 0 < v)
    (hrel : 1/r = 1/q - α/3)
    {p₁ p₂ : ℝ≥0∞} [ENNReal.HolderTriple p₁ p₂ 2]
    [ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal v) (ENNReal.ofReal (6/5 : ℝ))]
    (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (f : κ → ℝ → Space → ℝ) (g : κ → ℝ → Space → ℂ)
    (hf : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => f n z.1 z.2) (volume.prod volume))
    (hg : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => g n z.1 z.2) (volume.prod volume))
    (hff : ∀ n, mixedNorm volume volume p₁ (ENNReal.ofReal q) (f n) ≠ ∞)
    (hgf : ∀ n, mixedNorm volume volume p₂ (ENNReal.ofReal v) (g n) ≠ ∞)
    (hsmall :
      (Tendsto (fun n => mixedNorm volume volume p₁ (ENNReal.ofReal q) (f n)) l (𝓝 0) ∧
        ∃ B : ℝ≥0, ∀ n, mixedNorm volume volume p₂ (ENNReal.ofReal v) (g n) ≤ B) ∨
      ((∃ B : ℝ≥0, ∀ n, mixedNorm volume volume p₁ (ENNReal.ofReal q) (f n) ≤ B) ∧
        Tendsto (fun n => mixedNorm volume volume p₂ (ENNReal.ofReal v) (g n)) l (𝓝 0))) :
    (∀ n, forcingNorm (fun t x => rieszConvolution α c (f n t) x • g n t x) ≠ ∞) ∧
    Tendsto (fun n => forcingNorm (fun t x => rieszConvolution α c (f n t) x • g n t x)) l (𝓝 0) := by
  obtain ⟨C, hC⟩ := riesz_product_estimate hH hq1 hqα hr hv hrel hp₁ hp₂
  refine ⟨fun n => (hC (f n) (g n) (hf n) (hg n) (hff n) (hgf n)).1, ?_⟩
  rcases hsmall with ⟨ht, B, hB⟩ | ⟨⟨B, hB⟩, ht⟩
  · apply vanish_of_bound (C := (C : ℝ≥0∞) * B)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) ht
    intro n
    calc
      _ ≤ (C : ℝ≥0∞) * mixedNorm volume volume p₁ (ENNReal.ofReal q) (f n) *
          mixedNorm volume volume p₂ (ENNReal.ofReal v) (g n) :=
        (hC (f n) (g n) (hf n) (hg n) (hff n) (hgf n)).2
      _ ≤ (C : ℝ≥0∞) * mixedNorm volume volume p₁ (ENNReal.ofReal q) (f n) * B :=
        mul_le_mul' le_rfl (hB n)
      _ = ((C : ℝ≥0∞) * B) * mixedNorm volume volume p₁ (ENNReal.ofReal q) (f n) := by ring
  · apply vanish_of_bound (C := (C : ℝ≥0∞) * B)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) ht
    intro n
    exact (hC (f n) (g n) (hf n) (hg n) (hff n) (hgf n)).2.trans
      (mul_le_mul' (mul_le_mul' le_rfl (hB n)) le_rfl)

end HartreeF.FiniteProfileRieszMixed
