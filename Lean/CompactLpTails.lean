import UniformIMSEnergy
import Mathlib.Topology.MetricSpace.Pseudo.Basic

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation

/-- Exterior restriction as an actual map on the Lp quotient. -/
def exteriorLp {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (n : ℕ) (f : Lp E p (volume : Measure Space)) : Lp E p (volume : Measure Space) :=
  MemLp.toLp (exteriorTail n f)
    (MemLp.indicator (isOpen_lt continuous_const continuous_norm).measurableSet.nullMeasurableSet
      (Lp.memLp f))

theorem exteriorLp_norm {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (n : ℕ) (f : Lp E p (volume : Measure Space)) :
    ‖exteriorLp n f‖ = (eLpNorm (exteriorTail n f) p volume).toReal := by
  exact Lp.norm_toLp _ _

/-- Restriction is contractive for the actual Lp distance. -/
theorem exteriorLp_lipschitz {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (n : ℕ) :
    LipschitzWith 1 (exteriorLp (E := E) (p := p) n) := by
  apply LipschitzWith.of_edist_le
  intro f g
  unfold exteriorLp
  erw [Lp.edist_toLp_toLp, Lp.edist_def]
  change eLpNorm
    (({x : Space | (n : ℝ) < ‖x‖}.indicator (f : Space → E)) -
      ({x : Space | (n : ℝ) < ‖x‖}.indicator (g : Space → E))) p volume ≤ _
  have he : (({x : Space | (n : ℝ) < ‖x‖}.indicator (f : Space → E)) -
      ({x : Space | (n : ℝ) < ‖x‖}.indicator (g : Space → E))) =
      {x : Space | (n : ℝ) < ‖x‖}.indicator ((f : Space → E) - (g : Space → E)) := by
    funext x
    by_cases hx : (n : ℝ) < ‖x‖ <;> simp [Set.indicator, hx]
  rw [he]
  exact eLpNorm_indicator_le _
    (isOpen_lt continuous_const continuous_norm).measurableSet.nullMeasurableSet

/-- Every actual finite-Lp exterior restriction tends strongly to zero. -/
theorem exteriorLp_norm_tendsto_zero {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) (f : Lp E p (volume : Measure Space)) :
    Tendsto (fun n => ‖exteriorLp n f‖) atTop (𝓝 0) := by
  simp_rw [exteriorLp_norm]
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp
      (exteriorTail_eLpNorm_tendsto_zero (Lp.memLp f) hp0 hpt)

/-- One sufficiently large radius works on a whole compact Lp family and a fixed Lp neighborhood. -/
theorem compact_exteriorLp_uniform_neighborhood {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {K : Set (Lp E p (volume : Measure Space))} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ K, ∀ g : Lp E p (volume : Measure Space),
      dist g f < ε / 4 → ‖exteriorLp n g‖ < ε := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) Fact.out)
  obtain ⟨T, _hTK, hT, hcover⟩ := hK.finite_cover_balls (show 0 < ε / 4 by positivity)
  have hev : ∀ᶠ n : ℕ in atTop, ∀ a ∈ hT.toFinset, ‖exteriorLp n a‖ < ε / 2 := by
    apply hT.toFinset.eventually_all.mpr
    intro a _ha
    exact (exteriorLp_norm_tendsto_zero hp0 hpt a).eventually_lt_const (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro n hn f hf g hgf
  obtain ⟨a, ha, hfa⟩ : ∃ a ∈ T, f ∈ ball a (ε / 4) := by
    simpa only [mem_iUnion, exists_prop] using hcover hf
  have htail := hN n hn a (hT.mem_toFinset.mpr ha)
  have hdist : dist g a < ε / 2 := by
    have htri := dist_triangle g f a
    have hfa' : dist f a < ε / 4 := hfa
    linarith
  have hcontr := (exteriorLp_lipschitz (E := E) (p := p) n).dist_le_mul g a
  simp only [NNReal.coe_one, one_mul] at hcontr
  have hnorm : ‖exteriorLp n g‖ ≤ ‖exteriorLp n a‖ + dist (exteriorLp n g) (exteriorLp n a) := by
    simpa only [dist_eq_norm, norm_sub_rev] using
      norm_le_norm_add_norm_sub (exteriorLp n a) (exteriorLp n g)
  linarith

/-- Compact finite-Lp families have genuinely uniform exterior tails. -/
theorem compact_exteriorLp_uniform {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞)
    {K : Set (Lp E p (volume : Measure Space))} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ K, ‖exteriorLp n f‖ < ε := by
  obtain ⟨N, hN⟩ := compact_exteriorLp_uniform_neighborhood hpt hK hε
  exact ⟨N, fun n hn f hf => hN n hn f hf f (by simpa using (show 0 < ε / 4 by positivity))⟩

#print axioms exteriorLp_norm
#print axioms exteriorLp_lipschitz
#print axioms exteriorLp_norm_tendsto_zero
#print axioms compact_exteriorLp_uniform_neighborhood
#print axioms compact_exteriorLp_uniform
end HartreeF.ComplexIMS
