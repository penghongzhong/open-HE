import FActualMaximalMildTrajectory

/-! The literal compact Duhamel class and the native local trajectory class.
Critical-gradient membership is expressed by actual Bochner representatives;
no fixed-point, endpoint-output, or maximality premise is included. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121LiteralClass
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
  CriticalUniqueness SobolevStretch StationarySelfTest Retarded ActualStrichartz
  ForcingDomain EndpointOutput MaximalTrajectory

def LiteralMildOn (alpha kernel a b : ℝ) (q : ℝ → EnergyState) : Prop :=
  ∀ t : Icc a b, ∀ φ : FreeFlow.Test,
    energyDistribution (q t) φ =
      FreeFlow.free ((t : ℝ) - a) (energyDistribution (q a)) φ + Complex.I *
        ∫ z in Ioc a (t : ℝ), ∫ x,
          freeTest ((t : ℝ) - z) φ x • forcing alpha kernel (energyValue (q z)) x

theorem literal_mild_iff_path_mild {alpha kernel a b : ℝ}
    (hab : a ≤ b) (q : ℝ → EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hq : ∀ t : Icc a b, energyPath _ u t = q t) :
    LiteralMildOn alpha kernel a b q ↔ IsMildHartreePath hab alpha kernel (q a) u := by
  have hext (z : ℝ) (hz : z ∈ Icc a b) :
      extendEnergyPath hab (energyPath _ u) z = q z :=
    (extendEnergyPath_val hab (energyPath _ u) ⟨z, hz⟩).trans (hq ⟨z, hz⟩)
  have hint (t : Icc a b) (φ : FreeFlow.Test) :
      (∫ z in Ioc a (t : ℝ), ∫ x,
        freeTest ((t : ℝ) - z) φ x • forcing alpha kernel (energyValue (q z)) x) =
      ∫ z in Ioc a (t : ℝ), ∫ x,
        freeTest ((t : ℝ) - z) φ x •
          forcing alpha kernel (energyValue (extendEnergyPath hab (energyPath _ u) z)) x := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    rw [hext z ⟨hz.1.le, hz.2.trans t.property.2⟩]
  unfold LiteralMildOn IsMildHartreePath
  constructor
  · intro h t φ
    rw [hq, ← hint]
    exact h t φ
  · intro h t φ
    have ht := h t φ
    rw [hq, ← hint] at ht
    exact ht

theorem exists_native_path_of_literal {alpha kernel a b : ℝ}
    (hab : a ≤ b) (q : ℝ → EnergyState) (hc : ContinuousOn q (Icc a b))
    (g : Fin 3 → CriticalGradient (intervalMeasure a b))
    (hg : ∀ j : Fin 3, ∀ᵐ t ∂intervalMeasure a b,
      energyGradientDistribution j (q t) = Lp.toTemperedDistribution (g j t))
    (hmild : LiteralMildOn alpha kernel a b q) :
    ∃ u : CriticalPath (intervalMeasure a b),
      (∀ t : Icc a b, energyPath _ u t = q t) ∧
      IsMildHartreePath hab alpha kernel (q a) u := by
  let v : C(Icc a b, EnergyState) := ⟨fun t => q t, hc.continuous_restrict⟩
  let u : CriticalPath (intervalMeasure a b) := ⟨(v, g), hg⟩
  have hu (t : Icc a b) : energyPath _ u t = q t := rfl
  exact ⟨u, hu, (literal_mild_iff_path_mild hab q u hu).mp hmild⟩

structure LiteralLocalSolution (alpha kernel s : ℝ) (f : EnergyState) where
  domain : Set ℝ
  state : ℝ → EnergyState
  domain_open : IsOpen domain
  domain_connected : OrdConnected domain
  center_mem : s ∈ domain
  continuous : ContinuousOn state domain
  initial : state s = f
  critical : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ domain →
    ∃ g : Fin 3 → CriticalGradient (intervalMeasure a b),
      ∀ j : Fin 3, ∀ᵐ t ∂intervalMeasure a b,
        energyGradientDistribution j (state t) = Lp.toTemperedDistribution (g j t)
  mild : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ domain →
    LiteralMildOn alpha kernel a b state

def LiteralLocalSolution.toNative {alpha kernel s : ℝ} {f : EnergyState}
    (U : LiteralLocalSolution alpha kernel s f) : LocalMildTrajectory alpha kernel s f where
  domain := U.domain
  state := U.state
  domain_open := U.domain_open
  domain_connected := U.domain_connected
  center_mem := U.center_mem
  continuous := U.continuous
  initial := U.initial
  compact := by
    intro a b hab hI
    obtain ⟨g, hg⟩ := U.critical hab hI
    exact exists_native_path_of_literal hab U.state (U.continuous.mono hI) g hg (U.mild hab hI)

def ofNative {alpha kernel s : ℝ} {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) : LiteralLocalSolution alpha kernel s f where
  domain := U.domain
  state := U.state
  domain_open := U.domain_open
  domain_connected := U.domain_connected
  center_mem := U.center_mem
  continuous := U.continuous
  initial := U.initial
  critical := by
    intro a b hab hI
    refine ⟨fun j => criticalGradient _ j (U.path hab hI), ?_⟩
    intro j
    filter_upwards [(U.path hab hI).property j] with t ht
    change energyGradientDistribution j (energyPath _ (U.path hab hI) t) =
      Lp.toTemperedDistribution (criticalGradient _ j (U.path hab hI) t) at ht
    simpa only [U.path_agrees hab hI] using ht
  mild := by
    intro a b hab hI
    exact (literal_mild_iff_path_mild hab U.state (U.path hab hI)
      (U.path_agrees hab hI)).mpr (U.path_mild hab hI)

/-- Both translations preserve the original domain and the state at every
real time, including arbitrary outside-domain values. -/
theorem translations_preserve_domain_state {alpha kernel s : ℝ} {f : EnergyState}
    (U : LiteralLocalSolution alpha kernel s f) (V : LocalMildTrajectory alpha kernel s f) :
    U.toNative.domain = U.domain ∧ U.toNative.state = U.state ∧
      (ofNative V).domain = V.domain ∧ (ofNative V).state = V.state :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The native maximal solution is maximal against every literal-class
competitor, with equality of the same states on the competitor's entire domain. -/
theorem actual_maximal_among_literal_solutions (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hOrd : OrdinaryHLS alpha kernel)
    (s : ℝ) (f : EnergyState) (V : LiteralLocalSolution alpha kernel s f) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s f
    V.domain ⊆ M.domain ∧ EqOn M.state V.state V.domain ∧
      (M.domain ⊆ V.domain → V.domain = M.domain ∧ EqOn V.state M.state M.domain) := by
  intro M
  have hsub : V.domain ⊆ M.domain := subset_maximalDomain V.toNative
  have hag : EqOn M.state V.state V.domain := fun _ ht =>
    maximalState_agrees hDensity hSob h0 hfree hret hOrd V.toNative ht
  refine ⟨hsub, hag, ?_⟩
  intro h
  exact ⟨Subset.antisymm hsub h, fun _ ht => (hag (h ht)).symm⟩

end HartreeF.Paper121LiteralClass
