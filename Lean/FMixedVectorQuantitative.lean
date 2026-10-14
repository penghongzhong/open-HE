import FActualVectorInputConsumer
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.TimeHolder
open MeasureTheory ForcingDomain GradientMajorants SobolevStretch
open WeakHartreeProduct DerivativeMajorization DerivativeMajorizationReview
open scoped ENNReal NNReal RealInnerProductSpace

/-- Taking a pointwise norm preserves the extended mixed norm. -/
theorem mixed_norm_norm_eq {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞) (f : T → Space → E)
    (hf : AEStronglyMeasurable (fun z : T × Space => f z.1 z.2) (mu.prod volume)) :
    mixedNorm mu volume p q (fun t x => ‖f t x‖) = mixedNorm mu volume p q f := by
  unfold mixedNorm
  apply eLpNorm_congr_ae
  filter_upwards [hf.prodMk_left] with t ht
  exact eLpNorm_norm (f t) ht

/-- Exact real/extended transfer after a.e. spatial finiteness, with no
outer time-norm finiteness assumption. -/
theorem real_slice_mixed_eq {T E : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (f : T → Space → E)
    (hf : AEStronglyMeasurable (fun z : T × Space => f z.1 z.2) (mu.prod volume))
    (hs : ∀ᵐ t ∂mu, MemLp (f t) q volume) :
    eLpNorm (fun t => (eLpNorm (f t) q volume).toReal) p mu = mixedNorm mu volume p q f := by
  exact (finite_extended_norm_bridge mu p _
    (spatial_lp_time_measurable mu volume q hq0 hqtop f hf)
    (hs.mono fun _ ht => ht.eLpNorm_ne_top)).symm

/-- Two pointwise vector norms quantitatively dominate the mixed norm. -/
theorem mixed_norm_le_add_of_domination {T E F G : Type*} [MeasurableSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (mu : Measure T) [SigmaFinite mu] (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hqtop : q ≠ ∞)
    (f : T → Space → E) (g : T → Space → F) (h : T → Space → G)
    (hf : AEStronglyMeasurable (fun z : T × Space => f z.1 z.2) (mu.prod volume))
    (hg : AEStronglyMeasurable (fun z : T × Space => g z.1 z.2) (mu.prod volume))
    (hh : AEStronglyMeasurable (fun z : T × Space => h z.1 z.2) (mu.prod volume))
    (hdom : ∀ᵐ t ∂mu, ∀ᵐ x ∂volume, ‖f t x‖ ≤ ‖g t x‖ + ‖h t x‖) :
    mixedNorm mu volume p q f ≤ mixedNorm mu volume p q g + mixedNorm mu volume p q h := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hq)
  have hm := spatial_lp_time_measurable mu volume q hq0 hqtop f hf
  have hs : ∀ᵐ t ∂mu, eLpNorm (f t) q volume ≤ eLpNorm (g t) q volume + eLpNorm (h t) q volume := by
    filter_upwards [hf.prodMk_left, hg.prodMk_left, hh.prodMk_left, hdom] with t hft hgt hht hdt
    have htri := eLpNorm_add_le (f := fun x => ‖g t x‖) (g := fun x => ‖h t x‖) (μ := volume) hq
    rw [eLpNorm_norm _ hgt, eLpNorm_norm _ hht] at htri
    exact (eLpNorm_mono_ae_real hft hdt).trans htri
  have ht : eLpNorm (fun t => eLpNorm (f t) q volume) p mu ≤
      eLpNorm (fun t => eLpNorm (g t) q volume + eLpNorm (h t) q volume) p mu := by
    apply eLpNorm_mono_enorm_ae hm
    simpa only [enorm_eq_self] using hs
  exact ht.trans (eLpNorm_add_le hp)

end HartreeF.TimeHolder
