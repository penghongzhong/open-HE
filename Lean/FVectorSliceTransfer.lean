import FActualFullGradientMembership
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- The real slice norm is used only after spatial finiteness is established. -/
theorem real_slice_time_memLp_of_mixed {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (f : T → Space → E)
    (hf : AEStronglyMeasurable (fun z : T × Space => f z.1 z.2) (mu.prod volume))
    (hs : ∀ᵐ t ∂mu, MemLp (f t) q volume)
    (hfin : mixedNorm mu volume p q f ≠ ∞) :
    MemLp (fun t => (eLpNorm (f t) q volume).toReal) p mu := by
  have hm := spatial_lp_time_measurable mu volume q hq0 hqtop f hf
  have hsfin : ∀ᵐ t ∂mu, eLpNorm (f t) q volume ≠ ∞ := hs.mono fun _ ht => ht.eLpNorm_ne_top
  change eLpNorm (fun t => (eLpNorm (f t) q volume).toReal) p mu < ∞
  rw [← finite_extended_norm_bridge mu p _ hm hsfin]
  exact lt_top_iff_ne_top.mpr hfin

/-- Domination by two vector norms transfers time membership to the actual
slice norm and its norm-amplitude version. Spatial membership is retained. -/
theorem real_slice_time_domination {T E F G : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞) (hq : 1 ≤ q) (hqtop : q ≠ ∞)
    (f : T → Space → E) (g : T → Space → F) (h : T → Space → G)
    (hf : AEStronglyMeasurable (fun z : T × Space => f z.1 z.2) (mu.prod volume))
    (hg : ∀ᵐ t ∂mu, MemLp (g t) q volume)
    (hh : ∀ᵐ t ∂mu, MemLp (h t) q volume)
    (hgt : MemLp (fun t => (eLpNorm (g t) q volume).toReal) p mu)
    (hht : MemLp (fun t => (eLpNorm (h t) q volume).toReal) p mu)
    (hdom : ∀ᵐ t ∂mu, ∀ᵐ x ∂volume, ‖f t x‖ ≤ ‖g t x‖ + ‖h t x‖) :
    MemLp (fun t => (eLpNorm (f t) q volume).toReal) p mu ∧
    MemLp (fun t => (eLpNorm (fun x => ‖f t x‖) q volume).toReal) p mu := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hq)
  have hm := spatial_lp_time_toReal_measurable mu volume q hq0 hqtop f hf
  have ht : MemLp (fun t => (eLpNorm (f t) q volume).toReal) p mu := by
    apply (hgt.add hht).mono' hm
    filter_upwards [hf.prodMk_left, hg, hh, hdom] with t hft hgt' hht' hdt
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have htri := eLpNorm_add_le (f := fun x => ‖g t x‖) (g := fun x => ‖h t x‖)
      (μ := volume) hq
    rw [eLpNorm_norm _ hgt'.aestronglyMeasurable, eLpNorm_norm _ hht'.aestronglyMeasurable] at htri
    have hb := (eLpNorm_mono_ae_real hft hdt).trans htri
    have hr := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hgt'.eLpNorm_ne_top, hht'.eLpNorm_ne_top⟩) hb
    change (eLpNorm (fun x => f t x) q volume).toReal ≤
      (eLpNorm (g t) q volume).toReal + (eLpNorm (h t) q volume).toReal
    rwa [ENNReal.toReal_add hgt'.eLpNorm_ne_top hht'.eLpNorm_ne_top] at hr
  refine ⟨ht, (memLp_congr_ae ?_).mp ht⟩
  filter_upwards [hf.prodMk_left] with t hft
  exact (congrArg ENNReal.toReal (eLpNorm_norm (f t) hft)).symm

end HartreeF.TimeHolder
