import FTimeFiniteNormBridge
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal

/-- Distance tests prove Borel measurability in a second-countable metric target. -/
theorem measurable_of_dist_tests {T Y : Type*} [MeasurableSpace T]
    [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (g : T → Y) (h : ∀ y, Measurable (fun t => dist (g t) y)) : Measurable g := by
  have hb : IsTopologicalBasis {s : Set Y | ∃ y r, s = Metric.ball y r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨y, r, rfl⟩
      exact Metric.isOpen_ball
    · intro y s hys hs
      obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.mp hs y hys
      exact ⟨Metric.ball y r, ⟨y, r, rfl⟩, Metric.mem_ball_self hr, hrs⟩
  rw [BorelSpace.measurable_eq (α := Y), hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨y, r, rfl⟩
  exact measurableSet_lt (h y) measurable_const

/-- The finite-exponent spatial seminorm of a strongly jointly measurable function is measurable. -/
theorem spatial_lp_time_measurable_of_strong {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    (nu : Measure X) [SFinite nu] (q : ℝ≥0∞) (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    (f : T × X → E) (hf : StronglyMeasurable f) :
    Measurable (fun t => eLpNorm (fun x => f (t, x)) q nu) := by
  have hh := ((hf.enorm.pow_const q.toReal).lintegral_prod_right' (ν := nu)).pow_const (1 / q.toReal)
  convert hh using 1
  ext t
  exact eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop
    (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable

/-- Total spatial Lp class: the genuine class on MemLp slices, zero otherwise. -/
def spatialLpClass {T X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (nu : Measure X) (q : ℝ≥0∞) (f : T × X → E) (t : T) : Lp E q nu :=
  by
  classical
  exact if h : MemLp (fun x => f (t, x)) q nu then h.toLp (fun x => f (t, x)) else 0

/-- Strong joint measurability constructs, rather than assumes, the Lp-valued measurability. -/
theorem spatialLpClass_stronglyMeasurable {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [SeparableSpace E] (nu : Measure X) [SFinite nu] [IsSeparable nu]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [Fact (q ≠ ∞)]
    (f : T × X → E) (hf : StronglyMeasurable f) :
    StronglyMeasurable (spatialLpClass nu q f) := by
  classical
  let : MeasurableSpace (Lp E q nu) := borel (Lp E q nu)
  have : BorelSpace (Lp E q nu) := ⟨rfl⟩
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ q))
  have hqt : q ≠ ∞ := Fact.out
  have hgood : MeasurableSet {t | MemLp (fun x => f (t, x)) q nu} :=
    measurableSet_lt (spatial_lp_time_measurable_of_strong nu q hq0 hqt f hf) measurable_const
  apply Measurable.stronglyMeasurable
  apply measurable_of_dist_tests
  intro g
  have hd : Measurable (fun t => (eLpNorm (fun x => f (t, x) - g x) q nu).toReal) :=
    (spatial_lp_time_measurable_of_strong nu q hq0 hqt
      (fun z => f z - g z.2)
      (hf.sub ((Lp.stronglyMeasurable g).comp_measurable measurable_snd))).ennreal_toReal
  have hi : Measurable (fun t => if MemLp (fun x => f (t, x)) q nu then
      (eLpNorm (fun x => f (t, x) - g x) q nu).toReal else dist (0 : Lp E q nu) g) :=
    Measurable.ite hgood hd measurable_const
  convert hi using 1
  funext t
  by_cases ht : MemLp (fun x => f (t, x)) q nu
  · have he : edist (ht.toLp (fun x => f (t, x))) g =
        eLpNorm (fun x => f (t, x) - g x) q nu := by
      convert Lp.edist_toLp_toLp (fun x => f (t, x)) g ht (Lp.memLp g) using 1
      · rw [Lp.toLp_coeFn]
    simp only [spatialLpClass, dite_eq_left ht, ite_eq_left ht, Lp.dist_edist, he]
  · simp only [spatialLpClass, dite_eq_right ht, ite_eq_right ht]

/-- The total spatial class respects almost-everywhere equality on each slice. -/
theorem spatialLpClass_congr {T X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (nu : Measure X) (q : ℝ≥0∞)
    (f g : T × X → E) (t : T)
    (hfg : (fun x => f (t, x)) =ᵐ[nu] (fun x => g (t, x))) :
    spatialLpClass nu q f t = spatialLpClass nu q g t := by
  classical
  by_cases hf : MemLp (fun x => f (t, x)) q nu
  · have hg := (memLp_congr_ae hfg).mp hf
    simp only [spatialLpClass, dite_eq_left hf, dite_eq_left hg]
    exact hf.toLp_congr hg hfg
  · have hg : ¬ MemLp (fun x => g (t, x)) q nu :=
      fun hg => hf ((memLp_congr_ae hfg).mpr hg)
    simp only [spatialLpClass, dite_eq_right hf, dite_eq_right hg]

/-- Joint a.e. strong measurability constructs a measurable spatial Lq class. -/
theorem spatialLpClass_aestronglyMeasurable {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [SeparableSpace E] (mu : Measure T) (nu : Measure X) [SFinite nu] [IsSeparable nu]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [Fact (q ≠ ∞)]
    (f : T × X → E) (hf : AEStronglyMeasurable f (mu.prod nu)) :
    AEStronglyMeasurable (spatialLpClass nu q f) mu := by
  apply (spatialLpClass_stronglyMeasurable nu q (hf.mk f)
    hf.stronglyMeasurable_mk).aestronglyMeasurable.congr
  filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with t ht
  exact spatialLpClass_congr nu q (hf.mk f) f t (Filter.EventuallyEq.symm ht)

/-- A good slice of the constructed class represents the original function. -/
theorem spatialLpClass_coeFn {T X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (nu : Measure X) (q : ℝ≥0∞)
    (f : T × X → E) (t : T) (ht : MemLp (fun x => f (t, x)) q nu) :
    (spatialLpClass nu q f t : X → E) =ᵐ[nu] (fun x => f (t, x)) := by
  classical
  simp only [spatialLpClass, dite_eq_left ht]
  exact ht.coeFn_toLp

/-- The extended norm is preserved on every good slice. -/
theorem spatialLpClass_enorm {T X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (nu : Measure X) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (f : T × X → E) (t : T) (ht : MemLp (fun x => f (t, x)) q nu) :
    ‖spatialLpClass nu q f t‖ₑ = eLpNorm (fun x => f (t, x)) q nu := by
  classical
  simp only [spatialLpClass, dite_eq_left ht, Lp.enorm_toLp]

/-- The constructed Lq-valued function has exactly the original extended mixed norm. -/
theorem spatialLpClass_eLpNorm {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [SeparableSpace E] (mu : Measure T) (nu : Measure X) [SFinite nu] [IsSeparable nu]
    (p q : ℝ≥0∞) [Fact (1 ≤ q)] [Fact (q ≠ ∞)]
    (f : T × X → E) (hf : AEStronglyMeasurable f (mu.prod nu))
    (hslice : ∀ᵐ t ∂mu, MemLp (fun x => f (t, x)) q nu) :
    eLpNorm (spatialLpClass nu q f) p mu =
      mixedNorm mu nu p q (fun t x => f (t, x)) := by
  rw [← eLpNorm_enorm _ (spatialLpClass_aestronglyMeasurable mu nu q f hf)]
  apply eLpNorm_congr_ae
  filter_upwards [hslice] with t ht
  exact spatialLpClass_enorm nu q f t ht

/-- Finiteness of the mixed norm gives membership of the constructed Bochner function. -/
theorem spatialLpClass_memLp {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [SeparableSpace E] (mu : Measure T) (nu : Measure X) [SFinite nu] [IsSeparable nu]
    (p q : ℝ≥0∞) [Fact (1 ≤ q)] [Fact (q ≠ ∞)]
    (f : T × X → E) (hf : AEStronglyMeasurable f (mu.prod nu))
    (hslice : ∀ᵐ t ∂mu, MemLp (fun x => f (t, x)) q nu)
    (hfin : mixedNorm mu nu p q (fun t x => f (t, x)) ≠ ∞) :
    MemLp (spatialLpClass nu q f) p mu := by
  rw [memLp_iff, spatialLpClass_eLpNorm mu nu p q f hf hslice]
  exact lt_top_iff_ne_top.mpr hfin

/-- A genuine element of the iterated Bochner Lp space, constructed from joint data. -/
def jointLpRealization {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [SeparableSpace E] (mu : Measure T) (nu : Measure X) [SFinite nu] [IsSeparable nu]
    (p q : ℝ≥0∞) [Fact (1 ≤ q)] [Fact (q ≠ ∞)]
    (f : T × X → E) (hf : AEStronglyMeasurable f (mu.prod nu))
    (hslice : ∀ᵐ t ∂mu, MemLp (fun x => f (t, x)) q nu)
    (hfin : mixedNorm mu nu p q (fun t x => f (t, x)) ≠ ∞) : Lp (Lp E q nu) p mu :=
  (spatialLpClass_memLp mu nu p q f hf hslice hfin).toLp (spatialLpClass nu q f)

/-- The iterated Bochner element represents the joint function in the correct nested AE sense. -/
theorem jointLpRealization_coeFn {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [SeparableSpace E] (mu : Measure T) (nu : Measure X) [SFinite nu] [IsSeparable nu]
    (p q : ℝ≥0∞) [Fact (1 ≤ q)] [Fact (q ≠ ∞)]
    (f : T × X → E) (hf : AEStronglyMeasurable f (mu.prod nu))
    (hslice : ∀ᵐ t ∂mu, MemLp (fun x => f (t, x)) q nu)
    (hfin : mixedNorm mu nu p q (fun t x => f (t, x)) ≠ ∞) :
    ∀ᵐ t ∂mu, ∀ᵐ x ∂nu, jointLpRealization mu nu p q f hf hslice hfin t x = f (t, x) := by
  filter_upwards [(spatialLpClass_memLp mu nu p q f hf hslice hfin).coeFn_toLp,
    hslice] with t ht hts
  change ∀ᵐ x ∂nu, ((spatialLpClass_memLp mu nu p q f hf hslice hfin).toLp
    (spatialLpClass nu q f)) t x = f (t, x)
  rw [ht]
  exact spatialLpClass_coeFn nu q f t hts

/-- The extended norm of the actual Bochner element is the extended mixed norm. -/
theorem jointLpRealization_enorm {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [SeparableSpace E] (mu : Measure T) (nu : Measure X) [SFinite nu] [IsSeparable nu]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (q ≠ ∞)]
    (f : T × X → E) (hf : AEStronglyMeasurable f (mu.prod nu))
    (hslice : ∀ᵐ t ∂mu, MemLp (fun x => f (t, x)) q nu)
    (hfin : mixedNorm mu nu p q (fun t x => f (t, x)) ≠ ∞) :
    ‖jointLpRealization mu nu p q f hf hslice hfin‖ₑ =
      mixedNorm mu nu p q (fun t x => f (t, x)) := by
  rw [jointLpRealization, Lp.enorm_toLp, spatialLpClass_eLpNorm mu nu p q f hf hslice]

/-- The real norm is the finite mixed norm's real value, with finiteness proved first. -/
theorem jointLpRealization_norm {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [SeparableSpace E] (mu : Measure T) (nu : Measure X) [SFinite nu] [IsSeparable nu]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (q ≠ ∞)]
    (f : T × X → E) (hf : AEStronglyMeasurable f (mu.prod nu))
    (hslice : ∀ᵐ t ∂mu, MemLp (fun x => f (t, x)) q nu)
    (hfin : mixedNorm mu nu p q (fun t x => f (t, x)) ≠ ∞) :
    ‖jointLpRealization mu nu p q f hf hslice hfin‖ =
      (mixedNorm mu nu p q (fun t x => f (t, x))).toReal := by
  rw [jointLpRealization, Lp.norm_toLp, spatialLpClass_eLpNorm mu nu p q f hf hslice]

end HartreeF.TimeHolder
