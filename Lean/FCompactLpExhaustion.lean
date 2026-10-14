import FCoherentLpExhaustionAllExponents
import FIntervalLpRestriction
import FTimeFiniteNormBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IntervalNormExhaustion
open IntervalTimeTransport CriticalPathRestriction

def extendCompactLp {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) {a b : ℝ} (f : Lp E p (localMeasure a b)) : Lp E p (volume : Measure ℝ) :=
  ((memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (Lp.memLp f)).toLp
    ((Icc a b).indicator f)

theorem extendCompactLp_coeFn {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) {a b : ℝ} (f : Lp E p (localMeasure a b)) :
    (extendCompactLp p f : ℝ → E) =ᵐ[volume] (Icc a b).indicator f :=
  ((memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).2 (Lp.memLp f)).coeFn_toLp

theorem extendCompactLp_local {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) {a b : ℝ} (f : Lp E p (localMeasure a b)) :
    (extendCompactLp p f : ℝ → E) =ᵐ[localMeasure a b] f := by
  filter_upwards [ae_restrict_of_ae (extendCompactLp_coeFn p f),ae_restrict_mem measurableSet_Icc]
    with t ht hm
  simpa only [Set.indicator_of_mem hm] using ht

theorem extendCompactLp_norm {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) {a b : ℝ} (f : Lp E p (localMeasure a b)) :
    ‖extendCompactLp p f‖=‖f‖ := by
  rw [extendCompactLp,Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet,Lp.norm_def]

/-- Exhaustion constructs a global time-Lp class from actual local classes.
There is no global candidate, limiting state or integral finiteness premise. -/
theorem exists_global_Lp_of_coherent_compact {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a b : ℕ → ℝ) (ha : Antitone a) (hb : Monotone b)
    (f : ∀ n, Lp E p (localMeasure (a n) (b n))) (C : ℝ)
    (hbound : ∀ n, ‖f n‖ ≤ C)
    (hcoherent : ∀ n m, n ≤ m →
      (f m : ℝ → E) =ᵐ[localMeasure (a n) (b n)] f n) :
    ∃ F : Lp E p (volume : Measure ℝ), ‖F‖ ≤ C ∧
      (∀ n, (F : ℝ → E) =ᵐ[localMeasure (a n) (b n)] f n) ∧
      (∀ᵐ t ∂volume, t ∉ ⋃ n, Icc (a n) (b n) → F t=0) := by
  let g : ℕ → Lp E p (volume : Measure ℝ) := fun n => extendCompactLp p (f n)
  have hg : ∀ n, ‖g n‖ ≤ C := fun n =>
    (extendCompactLp_norm p (f n)).le.trans (hbound n)
  have hsupport : ∀ n, ∀ᵐ t ∂volume, t ∉ Icc (a n) (b n) → g n t=0 := by
    intro n
    filter_upwards [extendCompactLp_coeFn p (f n)] with t ht
    intro hm
    simpa only [Set.indicator_of_notMem hm] using ht
  have hcompat : ∀ n m, n ≤ m → ∀ᵐ t ∂volume,
      t ∈ Icc (a n) (b n) → g m t=g n t := by
    intro n m hnm
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [extendCompactLp_local p (f n),
      ae_mono (localMeasure_mono (ha hnm) (hb hnm)) (extendCompactLp_local p (f m)),
      hcoherent n m hnm] with t hn hm he
    exact hm.trans (he.trans hn.symm)
  obtain ⟨F,hFC,hFlocal,hFzero⟩ := exists_coherent_Lp_exhaustion
    (fun n => Icc (a n) (b n)) g C hg hsupport hcompat
  refine ⟨F,hFC,?_,hFzero⟩
  intro n
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).mpr (hFlocal n),
    extendCompactLp_local p (f n)] with t ht hg
  exact ht.trans hg

/-- The coherence needed above is produced from agreement with one actual
spacetime field. No global measurability or global Lp representative is assumed. -/
theorem exists_global_nestedLp_of_actual_compact {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (a b : ℕ → ℝ) (ha : Antitone a) (hb : Monotone b)
    (f : ∀ n, Lp (Lp E r ν) p (localMeasure (a n) (b n))) (g : ℝ → X → E) (C : ℝ)
    (hbound : ∀ n, ‖f n‖ ≤ C)
    (hactual : ∀ n, ∀ᵐ t ∂localMeasure (a n) (b n), (f n t : X → E) =ᵐ[ν] g t) :
    ∃ F : Lp (Lp E r ν) p (volume : Measure ℝ), ‖F‖ ≤ C ∧
      (∀ᵐ t ∂volume.restrict (⋃ n, Icc (a n) (b n)), (F t : X → E) =ᵐ[ν] g t) ∧
      (∀ᵐ t ∂volume, t ∉ ⋃ n, Icc (a n) (b n) → F t=0) := by
  have hcoherent : ∀ n m, n ≤ m →
      (f m : ℝ → Lp E r ν) =ᵐ[localMeasure (a n) (b n)] f n := by
    intro n m hnm
    filter_upwards [hactual n,ae_mono (localMeasure_mono (ha hnm) (hb hnm)) (hactual m)]
      with t hn hm
    exact Lp.ext (hm.trans hn.symm)
  obtain ⟨F,hFC,hFlocal,hFzero⟩ := exists_global_Lp_of_coherent_compact p a b ha hb
    f C hbound hcoherent
  have hact : ∀ᵐ t ∂volume, ∀ n, t ∈ Icc (a n) (b n) → (f n t : X → E) =ᵐ[ν] g t :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_Icc).mp (hactual n)
  have hloc : ∀ᵐ t ∂volume, ∀ n, t ∈ Icc (a n) (b n) → F t=f n t :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' measurableSet_Icc).mp (hFlocal n)
  refine ⟨F,hFC,?_,hFzero⟩
  filter_upwards [ae_restrict_of_ae hact,ae_restrict_of_ae hloc,
    ae_restrict_mem (MeasurableSet.iUnion fun _ => measurableSet_Icc)] with t ht hl hm
  obtain ⟨n,hn⟩ := mem_iUnion.mp hm
  rw [hl n hn]
  exact ht n hn

/-- A constructed global class gives the literal mixed norm of its actual
spacetime representative on the union, with the same constant. -/
theorem actual_mixedNorm_le_of_global_nestedLp {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (I : Set ℝ) (F : Lp (Lp E r ν) p (volume : Measure ℝ)) (g : ℝ → X → E)
    {C : ℝ} (hbound : ‖F‖ ≤ C)
    (hactual : ∀ᵐ t ∂volume.restrict I, (F t : X → E) =ᵐ[ν] g t) :
    TimeHolder.mixedNorm (volume.restrict I) ν p r g ≤ ENNReal.ofReal C := by
  calc
    _ = eLpNorm (fun t => ‖F t‖ₑ) p (volume.restrict I) := by
      apply eLpNorm_congr_ae
      filter_upwards [hactual] with t ht
      exact (eLpNorm_congr_ae ht.symm).trans (Lp.enorm_def _).symm
    _ = eLpNorm F p (volume.restrict I) :=
      eLpNorm_enorm _ ((Lp.aestronglyMeasurable F).mono_measure Measure.restrict_le_self)
    _ ≤ eLpNorm F p volume := eLpNorm_mono_measure F Measure.restrict_le_self
    _ = ENNReal.ofReal ‖F‖ := (Lp.enorm_def F).symm.trans (ofReal_norm F).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hbound

theorem actual_mixedNorm_le_of_coherent_compact {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (a b : ℕ → ℝ) (ha : Antitone a) (hb : Monotone b)
    (f : ∀ n, Lp (Lp E r ν) p (localMeasure (a n) (b n))) (g : ℝ → X → E) (C : ℝ)
    (hbound : ∀ n, ‖f n‖ ≤ C)
    (hactual : ∀ n, ∀ᵐ t ∂localMeasure (a n) (b n), (f n t : X → E) =ᵐ[ν] g t) :
    TimeHolder.mixedNorm (volume.restrict (⋃ n, Icc (a n) (b n))) ν p r g ≤
      ENNReal.ofReal C := by
  obtain ⟨F,hFC,hF,_⟩ := exists_global_nestedLp_of_actual_compact ν p r a b ha hb f g C
    hbound hactual
  exact actual_mixedNorm_le_of_global_nestedLp ν p r _ F g hFC hF

#print axioms extendCompactLp
#print axioms extendCompactLp_coeFn
#print axioms extendCompactLp_local
#print axioms extendCompactLp_norm
#print axioms exists_global_Lp_of_coherent_compact
#print axioms exists_global_nestedLp_of_actual_compact
#print axioms actual_mixedNorm_le_of_global_nestedLp
#print axioms actual_mixedNorm_le_of_coherent_compact
end HartreeF.IntervalNormExhaustion
