import FCompactLinearWeakEquation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace Retarded FreeTestBounds SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport

/-- Only the usual compact tensor-test PDE identity. Its analytic integrability
requirements will be produced from the actual C_t energy and L1 source domains. -/
def CompactTestIdentity (a b : ℝ) (U F : ℝ → TD) : Prop :=
  ∀ η : TimeTest, tsupport η ⊆ Set.Ioo a b → ∀ φ : Test, HasCompactSupport φ →
    (∫ t in Set.Icc a b, weakOperator U η φ t) =
      ∫ t in Set.Icc a b, η t * F t φ

theorem CompactWeakEquation.toIdentity {a b : ℝ} {U F : ℝ → TD}
    (h : CompactWeakEquation a b U F) : CompactTestIdentity a b U F :=
  fun η hη φ hφ => (h η hη φ hφ).2.2

theorem energy_test_pair_continuousOn {a b : ℝ} (u : ℝ → EnergyState)
    (hu : ContinuousOn u (Set.Icc a b)) (φ : Test) :
    ContinuousOn (fun t => energyDistribution (u t) φ) (Set.Icc a b) :=
  ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution).continuous.comp_continuousOn hu

theorem energy_weakOperator_integrable {a b : ℝ} (u : ℝ → EnergyState)
    (hu : ContinuousOn u (Set.Icc a b)) (η : TimeTest) (φ : Test) :
    IntegrableOn (weakOperator (fun t => energyDistribution (u t)) η φ) (Set.Icc a b) := by
  have hc : ContinuousOn (weakOperator (fun t => energyDistribution (u t)) η φ) (Set.Icc a b) :=
    ((continuous_const.continuousOn.mul ((η.smooth 1).continuous_deriv_one.continuousOn)).mul
      (energy_test_pair_continuousOn u hu φ)).add
      (η.continuous.continuousOn.mul (energy_test_pair_continuousOn u hu (Δ φ)))
  exact hc.integrableOn_Icc

theorem source_time_test_integrable {a b : ℝ} (f : ℝ → SourceSpace)
    (hf : IntegrableOn f (Set.Icc a b)) (η : TimeTest) (φ : Test) :
    IntegrableOn (fun t => η t * Lp.toTemperedDistribution (f t) φ) (Set.Icc a b) := by
  have hi := (sourcePairCLM (φ.toLp 6 volume)).integrable_comp hf
  have hp : IntegrableOn (fun t => Lp.toTemperedDistribution (f t) φ) (Set.Icc a b) :=
    hi.congr (Eventually.of_forall (fun t => sourcePairCLM_test φ (f t)))
  exact hp.bdd_mul η.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun t => SchwartzMap.norm_le_seminorm ℝ η t))

/-- No unproved scalar integrability assumption is needed at the PDE input. -/
theorem compactWeakEquation_of_actual_domains {a b : ℝ} (u : ℝ → EnergyState)
    (hu : ContinuousOn u (Set.Icc a b)) (f : ℝ → SourceSpace)
    (hf : IntegrableOn f (Set.Icc a b))
    (hPDE : CompactTestIdentity a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (f t))) :
    CompactWeakEquation a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (f t)) :=
  fun η hη φ hφ => ⟨energy_weakOperator_integrable u hu η φ,
    source_time_test_integrable f hf η φ, hPDE η hη φ hφ⟩

variable (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hret : OrdinaryRetardedStrichartz h0 C) (hab : a ≤ b)
  (E : CompatibleL1IntervalSource a b)

include hDensity hSob h0 hret hab

/-- Paper-facing linear bridge: ordinary compact PDE identity and the stated
actual domains produce the literal integral at any base time, without extra PDE,
time differentiability or scalar L2 hypotheses. -/
theorem actual_domain_distributional_duhamel_at
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b))
    (hu : CompactTestIdentity a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t)))
    (t₀ t : Set.Icc a b) (φ : FreeFlow.Test) :
    IntervalIntegrable (fun s => Lp.toTemperedDistribution (E.value s)
      (freeTest ((t : ℝ)-s) φ)) volume (t₀ : ℝ) (t : ℝ) ∧
    energyDistribution (u t) φ =
      FreeFlow.free ((t : ℝ)-(t₀ : ℝ)) (energyDistribution (u t₀)) φ - Complex.I *
        ∫ s in (t₀ : ℝ)..(t : ℝ),
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) :=
  compact_distributional_energy_literal_formula_at hDensity hSob h0 hret hab E
    hgen hUnique u hucont
    (compactWeakEquation_of_actual_domains u hucont E.value E.value_integrable hu) t₀ t φ

theorem actual_domain_distributional_iff_duhamel
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b)) :
    CompactTestIdentity a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t)) ↔
    ∀ t : Set.Icc a b, ∀ φ : FreeFlow.Test,
      energyDistribution (u t) φ =
        FreeFlow.free ((t : ℝ)-a) (energyDistribution (u a)) φ - Complex.I *
          ∫ s in Set.Ioc a (t : ℝ),
            Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  constructor
  · intro h
    exact (compact_distributional_energy_iff_literal_formula hDensity hSob h0 hret hab E
      hgen hUnique u hucont).mp
      (compactWeakEquation_of_actual_domains u hucont E.value E.value_integrable h)
  · intro h
    exact ((compact_distributional_energy_iff_literal_formula hDensity hSob h0 hret hab E
      hgen hUnique u hucont).mpr h).toIdentity

end HartreeF.LinearWeakEquation
