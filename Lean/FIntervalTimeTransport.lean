import FCriticalPathSpace
import Mathlib.Topology.Order.ProjIcc

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.IntervalTimeTransport
open CriticalPathSpace EnergySpace

abbrev localMeasure (a b : ℝ) : Measure ℝ := volume.restrict (Set.Icc a b)

/-- Inclusion identifies the actual subtype measure with restricted Lebesgue measure. -/
theorem inclusion_measurePreserving (a b : ℝ) :
    MeasurePreserving ((↑) : Set.Icc a b → ℝ) (intervalMeasure a b) (localMeasure a b) :=
  ⟨measurable_subtype_coe, map_comap_subtype_coe measurableSet_Icc volume⟩

instance intervalMeasure_finite (a b : ℝ) : IsFiniteMeasure (intervalMeasure a b) := by
  let : IsFiniteMeasure ((intervalMeasure a b).map ((↑) : Set.Icc a b → ℝ)) := by
    rw [(inclusion_measurePreserving a b).map_eq]
    infer_instance
  exact Measure.isFiniteMeasure_of_map measurable_subtype_coe.aemeasurable

/-- Clamping is a genuine continuous extension and is measure preserving on the interval. -/
theorem clamp_measurePreserving {a b : ℝ} (hab : a ≤ b) :
    MeasurePreserving (Set.projIcc a b hab) (localMeasure a b) (intervalMeasure a b) := by
  refine ⟨continuous_projIcc.measurable, ?_⟩
  rw [← (inclusion_measurePreserving a b).map_eq,
    Measure.map_map continuous_projIcc.measurable measurable_subtype_coe]
  have he : Set.projIcc a b hab ∘ ((↑) : Set.Icc a b → ℝ) = id := by
    funext t
    exact Set.projIcc_val hab t
  rw [he, Measure.map_id]

theorem ae_clamp {a b : ℝ} (hab : a ≤ b) {P : Set.Icc a b → Prop}
    (hP : ∀ᵐ t ∂intervalMeasure a b, P t) :
    ∀ᵐ t ∂localMeasure a b, P (Set.projIcc a b hab t) :=
  (clamp_measurePreserving hab).quasiMeasurePreserving.ae hP

/-- The same continuous homogeneous-energy curve, extended by endpoint values. -/
def extendEnergyPath {a b : ℝ} (hab : a ≤ b) (u : C(Set.Icc a b, EnergyState)) :
    C(ℝ, EnergyState) :=
  ⟨fun t => u (Set.projIcc a b hab t), u.continuous.comp continuous_projIcc⟩

@[simp] theorem extendEnergyPath_val {a b : ℝ} (hab : a ≤ b)
    (u : C(Set.Icc a b, EnergyState)) (t : Set.Icc a b) :
    extendEnergyPath hab u t = u t := by
  change u (Set.projIcc a b hab t) = u t
  rw [Set.projIcc_val]

/-- Exact Bochner Lp transport from subtype time to real restricted time. -/
def toLocalLp {a b : ℝ} (hab : a ≤ b) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) : Lp E p (intervalMeasure a b) →+ Lp E p (localMeasure a b) :=
  Lp.compMeasurePreserving (Set.projIcc a b hab) (clamp_measurePreserving hab)

theorem toLocalLp_coeFn {a b : ℝ} (hab : a ≤ b) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (f : Lp E p (intervalMeasure a b)) :
    toLocalLp hab p f =ᵐ[localMeasure a b] fun t => f (Set.projIcc a b hab t) :=
  Lp.coeFn_compMeasurePreserving f (clamp_measurePreserving hab)

theorem toLocalLp_norm {a b : ℝ} (hab : a ≤ b) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (f : Lp E p (intervalMeasure a b)) :
    ‖toLocalLp hab p f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (clamp_measurePreserving hab)

/-- Exact reverse transport for the eventual output CriticalPath coordinates. -/
def toIntervalLp (a b : ℝ) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) : Lp E p (localMeasure a b) →+ Lp E p (intervalMeasure a b) :=
  Lp.compMeasurePreserving ((↑) : Set.Icc a b → ℝ) (inclusion_measurePreserving a b)

theorem toIntervalLp_coeFn (a b : ℝ) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (f : Lp E p (localMeasure a b)) :
    toIntervalLp a b p f =ᵐ[intervalMeasure a b] fun t => f (t : ℝ) :=
  Lp.coeFn_compMeasurePreserving f (inclusion_measurePreserving a b)

theorem toIntervalLp_norm (a b : ℝ) {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (f : Lp E p (localMeasure a b)) :
    ‖toIntervalLp a b p f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (inclusion_measurePreserving a b)

/-- Both directions are inverses as Lp classes, including the degenerate interval. -/
theorem toIntervalLp_toLocalLp {a b : ℝ} (hab : a ≤ b)
    {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (f : Lp E p (intervalMeasure a b)) :
    toIntervalLp a b p (toLocalLp hab p f) = f := by
  change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : Set.projIcc a b hab ∘ ((↑) : Set.Icc a b → ℝ) = id := by
    funext t
    exact Set.projIcc_val hab t
  simp only [he, Lp.compMeasurePreserving_id_apply]

theorem toLocalLp_toIntervalLp {a b : ℝ} (hab : a ≤ b)
    {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞)
    (f : Lp E p (localMeasure a b)) :
    toLocalLp hab p (toIntervalLp a b p f) = f := by
  apply Lp.ext
  filter_upwards [toLocalLp_coeFn hab p (toIntervalLp a b p f),
    ae_clamp hab (toIntervalLp_coeFn a b p f), ae_restrict_mem measurableSet_Icc]
    with t ht hc hm
  rw [ht, hc, Set.projIcc_of_mem hab hm]

/-- Pulling a scalar norm profile through clamp preserves its extended norm,
without an extra measurability hypothesis. -/
theorem eLpNorm_clamp {a b : ℝ} (hab : a ≤ b)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E] (p : ℝ≥0∞) (f : Set.Icc a b → E) :
    eLpNorm (fun t => f (Set.projIcc a b hab t)) p (localMeasure a b) =
      eLpNorm f p (intervalMeasure a b) := by
  rw [← (inclusion_measurePreserving a b).map_eq,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).eLpNorm_map_measure]
  congr 1
  funext t
  exact congrArg f (Set.projIcc_val hab t)

end HartreeF.IntervalTimeTransport
