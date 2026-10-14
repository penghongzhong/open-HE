import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Constructions.Polish.Basic
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder

theorem simple_lp_jointly_measurable {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (s : SimpleFunc T (Lp E q nu)) :
    Measurable (fun z : T × X => s z.1 z.2) := by
  let : MeasurableSpace (Lp E q nu) := borel (Lp E q nu)
  let : BorelSpace (Lp E q nu) := ⟨rfl⟩
  let : Countable (Set.range s) := s.finite_range.countable.to_subtype
  have h : Measurable (fun z : (Set.range s) × X => z.1.val z.2) :=
    measurable_from_prod_countable_right (fun a => (Lp.stronglyMeasurable a.val).measurable)
  exact h.comp ((s.measurable.subtype_mk (h := fun t => ⟨t, rfl⟩)).comp measurable_fst |>.prodMk measurable_snd)


/-- A measurable choice of sufficiently accurate simple approximants gives jointly measurable
representatives at every approximation stage. -/
theorem exists_joint_lp_approximants {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : StronglyMeasurable g)
    (eps : ℕ → ℝ) (heps : ∀ n, 0 < eps n) :
    ∃ a : ℕ → T → Lp E q nu,
      (∀ n, Measurable (fun z : T × X => a n z.1 z.2)) ∧
      ∀ n t, dist (a n t) (g t) < eps n := by
  classical
  let : MeasurableSpace (Lp E q nu) := borel (Lp E q nu)
  have : BorelSpace (Lp E q nu) := ⟨rfl⟩
  have hex (n : ℕ) (t : T) : ∃ k, dist (hg.approx k t) (g t) < eps n := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hg.tendsto_approx t) (eps n) (heps n)
    exact ⟨N, hN N le_rfl⟩
  let k (n : ℕ) (t : T) : ℕ := Nat.find (hex n t)
  refine ⟨fun n t => hg.approx (k n t) t, ?_, ?_⟩
  · intro n
    exact Measurable.find
      (fun j => simple_lp_jointly_measurable nu q (hg.approx j))
      (fun j => (measurableSet_lt (((hg.approx j).stronglyMeasurable.dist hg).measurable)
        measurable_const).preimage measurable_fst)
      (fun z : T × X => hex n z.1)
  · intro n t
    exact Nat.find_spec (hex n t)



/-- Geometric approximation in Lp gives a fixed summable Cauchy control for representatives. -/
theorem joint_approximants_cauchy_bound {T X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (a : ℕ → T → Lp E q nu)
    (ha : ∀ n t, dist (a n t) (g t) < (1 / 2 : ℝ) ^ n) :
    ∀ t N n m, N ≤ n → N ≤ m →
      eLpNorm ((a n t : X → E) - (a m t : X → E)) q nu <
        ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N) := by
  intro t N n m hn hm
  rw [← Lp.edist_def, edist_dist]
  apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
  calc
    dist (a n t) (a m t) ≤ dist (a n t) (g t) + dist (g t) (a m t) := dist_triangle _ _ _
    _ < (1 / 2 : ℝ) ^ n + (1 / 2 : ℝ) ^ m := by
      simpa only [dist_comm (g t)] using add_lt_add (ha n t) (ha m t)
    _ ≤ (1 / 2 : ℝ) ^ N + (1 / 2 : ℝ) ^ N := by
      exact add_le_add (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn)
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm)
    _ = 2 * (1 / 2 : ℝ) ^ N := by ring

/-- The Cauchy control used by the representative construction has finite sum. -/
theorem joint_approximants_control_summable :
    (∑' n : ℕ, ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n)) ≠ ∞ := by
  exact ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2).tsum_ofReal_ne_top

/-- A geometrically controlled approximation tends to its given Lp class. -/
theorem joint_approximants_tendsto {T X E : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (a : ℕ → T → Lp E q nu)
    (ha : ∀ n t, dist (a n t) (g t) < (1 / 2 : ℝ) ^ n) (t : T) :
    Tendsto (fun n => a n t) atTop (𝓝 (g t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (ha n t).le)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))


/-- A measurable sequence admits a measurable selector agreeing with its limit at every
point where the sequence converges. -/
theorem exists_measurable_pointwise_limit_joint
    {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (F : ℕ → A → E) (hF : ∀ n, Measurable (F n)) :
    ∃ f : A → E, Measurable f ∧
      ∀ a, (∃ l, Tendsto (fun n => F n a) atTop (𝓝 l)) →
        Tendsto (fun n => F n a) atTop (𝓝 (f a)) := by
  classical
  let C : Set A := {a | ∃ l, Tendsto (fun n => F n a) atTop (𝓝 l)}
  have hC : MeasurableSet C := MeasureTheory.measurableSet_exists_tendsto hF
  let f : A → E := fun a => if h : a ∈ C then Classical.choose h else 0
  let G : ℕ → A → E := fun n a => if a ∈ C then F n a else 0
  have hG : ∀ n, Measurable (G n) := by
    intro n
    exact (hF n).piecewise hC measurable_const
  have hlim : ∀ a, Tendsto (fun n => G n a) atTop (𝓝 (f a)) := by
    intro a
    by_cases ha : a ∈ C
    · simpa only [G, f, ite_eq_left ha, dite_eq_left ha] using Classical.choose_spec ha
    · simpa only [G, f, ite_eq_right ha, dite_eq_right ha] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 0))
  refine ⟨f, measurable_of_tendsto_metrizable hG (tendsto_pi_nhds.mpr hlim), ?_⟩
  intro a ha
  have haC : a ∈ C := ha
  simpa only [f, dite_eq_left haC] using Classical.choose_spec haC



/-- A strongly measurable Lp-valued curve has a strongly jointly measurable representative,
with equality to its given Lp class on every time slice. -/
theorem exists_strong_joint_lp_representative {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : StronglyMeasurable g) :
    ∃ f : T × X → E, StronglyMeasurable f ∧
      ∀ t, (fun x => f (t, x)) =ᵐ[nu] (g t : X → E) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  obtain ⟨a, ha_meas, ha_dist⟩ := exists_joint_lp_approximants nu q g hg
    (fun n => (1 / 2 : ℝ) ^ n) (fun _ => by positivity)
  obtain ⟨f, hf, hflim⟩ := exists_measurable_pointwise_limit_joint
    (fun (n : ℕ) (z : T × X) => a n z.1 z.2) ha_meas
  refine ⟨f, hf.stronglyMeasurable, ?_⟩
  intro t
  have hcau := joint_approximants_cauchy_bound nu q g a ha_dist t
  have hae : ∀ᵐ x ∂nu, ∃ l, Tendsto (fun n => a n t x) atTop (𝓝 l) :=
    Lp.ae_tendsto_of_cauchy_eLpNorm
      (fun n => (Lp.stronglyMeasurable (a n t)).aestronglyMeasurable)
      (Fact.out : 1 ≤ q) joint_approximants_control_summable hcau
  have hlim : ∀ᵐ x ∂nu, Tendsto (fun n => a n t x) atTop (𝓝 (f (t, x))) :=
    hae.mono (fun x hx => hflim (t, x) hx)
  have hnorm := Lp.cauchy_tendsto_of_tendsto
    (fun n => (Lp.stronglyMeasurable (a n t)).aestronglyMeasurable)
    (fun x => f (t, x)) joint_approximants_control_summable hcau hlim
  have hmem := Lp.memLp_of_cauchy_tendsto (Fact.out : 1 ≤ q)
    (fun n => Lp.memLp (a n t)) (fun x => f (t, x)) hnorm
  have heq : hmem.toLp (fun x => f (t, x)) = g t :=
    tendsto_nhds_unique (Lp.tendsto_Lp_of_tendsto_eLpNorm _ hmem hnorm)
      (joint_approximants_tendsto nu q g a ha_dist t)
  simpa only [heq] using hmem.coeFn_toLp.symm

/-- An a.e. strongly measurable Lp curve has a jointly strongly measurable representative,
with the expected nested time/space a.e. equality. -/
theorem exists_ae_joint_lp_representative {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (mu : Measure T) (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : AEStronglyMeasurable g mu) :
    ∃ f : T × X → E, StronglyMeasurable f ∧
      ∀ᵐ t ∂mu, (fun x => f (t, x)) =ᵐ[nu] (g t : X → E) := by
  obtain ⟨f, hf, hfg⟩ := exists_strong_joint_lp_representative nu q
    (hg.mk g) hg.stronglyMeasurable_mk
  refine ⟨f, hf, ?_⟩
  filter_upwards [hg.ae_eq_mk] with t ht
  simpa only [ht] using hfg t


/-- A selected jointly strongly measurable representative of a strongly measurable Lp curve. -/
def strongJointLpRepresentative {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : StronglyMeasurable g) : T × X → E :=
  (exists_strong_joint_lp_representative nu q g hg).choose

theorem strongJointLpRepresentative_stronglyMeasurable {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : StronglyMeasurable g) :
    StronglyMeasurable (strongJointLpRepresentative nu q g hg) :=
  (exists_strong_joint_lp_representative nu q g hg).choose_spec.1

theorem strongJointLpRepresentative_slice {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : StronglyMeasurable g) (t : T) :
    (fun x => strongJointLpRepresentative nu q g hg (t, x)) =ᵐ[nu] (g t : X → E) :=
  (exists_strong_joint_lp_representative nu q g hg).choose_spec.2 t

theorem strongJointLpRepresentative_memLp {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : StronglyMeasurable g) (t : T) :
    MemLp (fun x => strongJointLpRepresentative nu q g hg (t, x)) q nu :=
  (memLp_congr_ae (strongJointLpRepresentative_slice nu q g hg t)).mpr (Lp.memLp (g t))

/-- Apply the construction to the strongly measurable modification of an AE-strong curve. -/
def aeJointLpRepresentative {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (mu : Measure T) (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : AEStronglyMeasurable g mu) : T × X → E :=
  strongJointLpRepresentative nu q (hg.mk g) hg.stronglyMeasurable_mk

theorem aeJointLpRepresentative_stronglyMeasurable {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (mu : Measure T) (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : AEStronglyMeasurable g mu) :
    StronglyMeasurable (aeJointLpRepresentative mu nu q g hg) :=
  strongJointLpRepresentative_stronglyMeasurable nu q (hg.mk g) hg.stronglyMeasurable_mk

theorem aeJointLpRepresentative_slice {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (mu : Measure T) (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : AEStronglyMeasurable g mu) :
    ∀ᵐ t ∂mu, (fun x => aeJointLpRepresentative mu nu q g hg (t, x)) =ᵐ[nu] (g t : X → E) := by
  filter_upwards [hg.ae_eq_mk] with t ht
  simpa only [aeJointLpRepresentative, ht] using strongJointLpRepresentative_slice nu q (hg.mk g) hg.stronglyMeasurable_mk t

theorem aeJointLpRepresentative_memLp {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    [CompleteSpace E] [SeparableSpace E] (mu : Measure T) (nu : Measure X) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] (g : T → Lp E q nu) (hg : AEStronglyMeasurable g mu) (t : T) :
    MemLp (fun x => aeJointLpRepresentative mu nu q g hg (t, x)) q nu :=
  strongJointLpRepresentative_memLp nu q (hg.mk g) hg.stronglyMeasurable_mk t

end HartreeF.TimeHolder
