import FIntervalTimeTransport

/-! Actual Bochner restriction to a nested compact time interval. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathRestriction
open EnergySpace CriticalPathSpace IntervalTimeTransport

variable {a b c d : ℝ}

/-- The literal inclusion of the smaller interval, with unchanged real time. -/
def intervalInclusion (hac : a ≤ c) (hdb : d ≤ b) : Set.Icc c d → Set.Icc a b :=
  fun t => ⟨t.val, hac.trans t.property.1, t.property.2.trans hdb⟩

theorem intervalInclusion_continuous (hac : a ≤ c) (hdb : d ≤ b) :
    Continuous (intervalInclusion hac hdb) :=
  continuous_subtype_val.subtype_mk _

theorem localMeasure_mono (hac : a ≤ c) (hdb : d ≤ b) :
    localMeasure c d ≤ localMeasure a b :=
  Measure.restrict_mono_set volume (fun _ ht => ⟨hac.trans ht.1, ht.2.trans hdb⟩)

theorem ae_intervalInclusion (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    {P : Set.Icc a b → Prop} (hP : ∀ᵐ t ∂intervalMeasure a b, P t) :
    ∀ᵐ t ∂intervalMeasure c d, P (intervalInclusion hac hdb t) := by
  have h := (inclusion_measurePreserving c d).quasiMeasurePreserving.ae
    (ae_mono (localMeasure_mono hac hdb) (ae_clamp (hac.trans (hcd.trans hdb)) hP))
  filter_upwards [h] with t ht
  have he : Set.projIcc a b (hac.trans (hcd.trans hdb)) (t : ℝ) =
      intervalInclusion hac hdb t :=
    Set.projIcc_of_mem _ (intervalInclusion hac hdb t).property
  simpa only [he] using ht

section Lp
variable {E : Type*} [NormedAddCommGroup E] {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (p : ℝ≥0∞)

/-- Shrinking the measure preserves the exact representative class. -/
def shrinkLp (h : ν ≤ μ) (f : Lp E p μ) : Lp E p ν :=
  ((Lp.memLp f).mono_measure h).toLp f

theorem shrinkLp_coeFn (h : ν ≤ μ) (f : Lp E p μ) :
    shrinkLp p h f =ᵐ[ν] f := MemLp.coeFn_toLp _

theorem shrinkLp_norm_le (h : ν ≤ μ) (f : Lp E p μ) :
    ‖shrinkLp p h f‖ ≤ ‖f‖ := by
  rw [shrinkLp, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure f h)

/-- Restrict an actual Bochner class by measure restriction and canonical transport. -/
def restrictIntervalLp (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (f : Lp E p (intervalMeasure a b)) : Lp E p (intervalMeasure c d) :=
  toIntervalLp c d p (shrinkLp p (localMeasure_mono hac hdb)
    (toLocalLp (hac.trans (hcd.trans hdb)) p f))

theorem restrictIntervalLp_coeFn (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (f : Lp E p (intervalMeasure a b)) :
    restrictIntervalLp p hac hcd hdb f =ᵐ[intervalMeasure c d]
      fun t => f (intervalInclusion hac hdb t) := by
  let g := toLocalLp (hac.trans (hcd.trans hdb)) p f
  have hs := (inclusion_measurePreserving c d).quasiMeasurePreserving.ae
    (shrinkLp_coeFn p (localMeasure_mono hac hdb) g)
  have hg := (inclusion_measurePreserving c d).quasiMeasurePreserving.ae
    (ae_mono (localMeasure_mono hac hdb)
      (toLocalLp_coeFn (hac.trans (hcd.trans hdb)) p f))
  filter_upwards [toIntervalLp_coeFn c d p (shrinkLp p (localMeasure_mono hac hdb) g),
    hs, hg] with t ht hs hg
  change (toIntervalLp c d p (shrinkLp p (localMeasure_mono hac hdb) g)) t = _
  rw [ht, hs, hg]
  exact congrArg f (Set.projIcc_of_mem _ (intervalInclusion hac hdb t).property)

theorem restrictIntervalLp_norm_le (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (f : Lp E p (intervalMeasure a b)) :
    ‖restrictIntervalLp p hac hcd hdb f‖ ≤ ‖f‖ := by
  rw [restrictIntervalLp, toIntervalLp_norm]
  exact (shrinkLp_norm_le p _ _).trans_eq (toLocalLp_norm _ p f)

end Lp
end HartreeF.CriticalPathRestriction
