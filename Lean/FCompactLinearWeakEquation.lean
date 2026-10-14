import FActualPDEToDuhamelRestart

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.LinearWeakEquation
open EnergySpace SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport

/-- The representation changes no spatial test-function values. -/
theorem compactSmooth_spatial_test_representation (f : V → ℂ)
    (hc : HasCompactSupport f) (hs : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ φ : Test, (φ : V → ℂ) = f ∧ HasCompactSupport φ :=
  ⟨hc.toSchwartzMap hs, rfl, hc⟩

/-- The same exact representation is available for every usual compact time test. -/
theorem compactSmooth_time_test_representation (f : ℝ → ℂ)
    (hc : HasCompactSupport f) (hs : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ η : TimeTest, (η : ℝ → ℂ) = f ∧ HasCompactSupport η :=
  ⟨hc.toSchwartzMap hs, rfl, hc⟩

/-- The usual compact spatial distribution tests, represented without changing
their functions: a compactly supported smooth function is a Schwartz function. -/
def CompactWeakEquation (a b : ℝ) (U F : ℝ → TD) : Prop :=
  ∀ η : TimeTest, tsupport η ⊆ Set.Ioo a b → ∀ φ : Test, HasCompactSupport φ →
    IntegrableOn (weakOperator U η φ) (Set.Icc a b) ∧
    IntegrableOn (fun t => η t * F t φ) (Set.Icc a b) ∧
    (∫ t in Set.Icc a b, weakOperator U η φ t) =
      ∫ t in Set.Icc a b, η t * F t φ

theorem WeakEquation.toCompact {a b : ℝ} {U F : ℝ → TD}
    (h : WeakEquation a b U F) : CompactWeakEquation a b U F :=
  fun η hη φ _ => h η hη φ

/-- Replacing the source by its actual Lp representative preserves the weak PDE. -/
theorem CompactWeakEquation.source_congr {a b : ℝ} {U F G : ℝ → TD}
    (h : CompactWeakEquation a b U F)
    (hFG : F =ᵐ[volume.restrict (Set.Icc a b)] G) : CompactWeakEquation a b U G := by
  intro η hη φ hφ
  obtain ⟨hUi, hFi, he⟩ := h η hη φ hφ
  have hae : (fun t => η t * F t φ) =ᵐ[volume.restrict (Set.Icc a b)]
      (fun t => η t * G t φ) := hFG.mono (fun _ ht => by dsimp; rw [ht])
  exact ⟨hUi, hFi.congr hae, he.trans (integral_congr_ae hae)⟩

theorem CompactWeakEquation.state_congr {a b : ℝ} {U V F : ℝ → TD}
    (h : CompactWeakEquation a b U F)
    (hUV : ∀ t ∈ Set.Icc a b, U t = V t) : CompactWeakEquation a b V F := by
  intro η hη φ hφ
  obtain ⟨hUi, hFi, he⟩ := h η hη φ hφ
  have hae : weakOperator U η φ =ᵐ[volume.restrict (Set.Icc a b)] weakOperator V η φ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [weakOperator, hUV t ht]
  exact ⟨hUi.congr hae, hFi, (integral_congr_ae hae).symm.trans he⟩

/-- Spatial differentiated tests are genuinely still compactly supported. -/
theorem neg_derivative_hasCompactSupport (v : V) (φ : Test) (hφ : HasCompactSupport φ) :
    HasCompactSupport (-∂_{v} φ : Test) := by
  have hd : HasCompactSupport (∂_{v} φ : Test) :=
    hφ.mono' ((subset_tsupport _).trans (SchwartzMap.tsupport_lineDerivOp_subset v φ))
  exact hd.comp_left (by simp : -(0 : ℂ) = 0)

theorem CompactWeakEquation.derivative {a b : ℝ} {U F : ℝ → TD}
    (h : CompactWeakEquation a b U F) (v : V) :
    CompactWeakEquation a b (fun t => ∂_{v} (U t)) (fun t => ∂_{v} (F t)) := by
  intro η hη φ hφ
  have he : weakOperator (fun t => ∂_{v} (U t)) η φ = weakOperator U η (-∂_{v} φ) :=
    funext (weakOperator_derivative U v η φ)
  simpa only [he, TemperedDistribution.lineDerivOp_apply_apply]
    using h η hη (-∂_{v} φ) (neg_derivative_hasCompactSupport v φ hφ)

theorem CompactWeakEquation.sub {a b : ℝ} {U V F G : ℝ → TD}
    (hU : CompactWeakEquation a b U F) (hV : CompactWeakEquation a b V G) :
    CompactWeakEquation a b (fun t => U t - V t) (fun t => F t - G t) := by
  intro η hη φ hφ
  obtain ⟨hUi, hFi, hUe⟩ := hU η hη φ hφ
  obtain ⟨hVi, hGi, hVe⟩ := hV η hη φ hφ
  have he : weakOperator (fun t => U t - V t) η φ =
      fun t => weakOperator U η φ t - weakOperator V η φ t :=
    funext (weakOperator_sub U V η φ)
  simp only [he, sub_apply, mul_sub]
  exact ⟨hUi.sub hVi, hFi.sub hGi,
    by rw [integral_sub hUi hVi, integral_sub hFi hGi, hUe, hVe]⟩

/-- Ordinary zero-source L2 uniqueness in the usual compact distributional tests.
Le Coz Definition2.3.1/Prop2.3.2, local interval specialization; see source map.
This is a generic linear analytic Prop, never a Hartree or energy-space premise. -/
structure OrdinaryL2CompactHomogeneousUniqueness : Prop where
  zero : ∀ (a b t₀ : ℝ), t₀ ∈ Set.Icc a b → ∀ z : ℝ → L2,
    ContinuousOn z (Set.Icc a b) →
    CompactWeakEquation a b (fun t => Lp.toTemperedDistribution (z t)) (fun _ => 0) →
    z t₀ = 0 → ∀ t ∈ Set.Icc a b, z t = 0

theorem OrdinaryL2CompactHomogeneousUniqueness.toSchwartz
    (h : OrdinaryL2CompactHomogeneousUniqueness) : OrdinaryL2HomogeneousUniqueness :=
  ⟨fun a b t₀ ht₀ z hcont hp hinit => h.zero a b t₀ ht₀ z hcont hp.toCompact hinit⟩

theorem compact_homogeneous_energy_zero (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    {K a b t₀ : ℝ} (hSob : OrdinarySobolev K) (ht₀ : t₀ ∈ Set.Icc a b)
    (u : ℝ → EnergyState) (hcont : ContinuousOn u (Set.Icc a b))
    (hPDE : CompactWeakEquation a b (fun t => energyDistribution (u t)) (fun _ => 0))
    (hinit : u t₀ = 0) : ∀ t ∈ Set.Icc a b, u t = 0 := by
  intro t ht
  apply energyState_eq_zero_of_gradients hSob (u t)
  intro j
  apply hUnique.zero a b t₀ ht₀ (fun s => energyGradient j (u s))
    ((energyGradient j).continuous.comp_continuousOn hcont) _ (by simp only [hinit, map_zero]) t ht
  have he (s : ℝ) : ∂_{coordinate j} (energyDistribution (u s)) =
      Lp.toTemperedDistribution (energyGradient j (u s)) := energyDistribution_derivative (u s) j
  simpa only [he, lineDerivOp_zero] using hPDE.derivative (coordinate j)

theorem compact_energy_weak_uniqueness (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    {K a b t₀ : ℝ} (hSob : OrdinarySobolev K) (ht₀ : t₀ ∈ Set.Icc a b)
    (u v : ℝ → EnergyState) (F : ℝ → TD)
    (hucont : ContinuousOn u (Set.Icc a b)) (hvcont : ContinuousOn v (Set.Icc a b))
    (hu : CompactWeakEquation a b (fun t => energyDistribution (u t)) F)
    (hv : CompactWeakEquation a b (fun t => energyDistribution (v t)) F)
    (hinit : u t₀ = v t₀) : ∀ t ∈ Set.Icc a b, u t = v t := by
  have hp : CompactWeakEquation a b (fun t => energyDistribution (u t - v t)) (fun _ => 0) := by
    simpa only [map_sub, sub_self] using hu.sub hv
  have hz := compact_homogeneous_energy_zero hUnique hSob ht₀ (fun t => u t - v t)
    (hucont.sub hvcont) hp (sub_eq_zero.mpr hinit)
  exact fun t ht => sub_eq_zero.mp (hz t ht)

variable (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hret : OrdinaryRetardedStrichartz h0 C) (hab : a ≤ b)
  (E : CompatibleL1IntervalSource a b)

include hDensity hSob h0 hret hab

/-- Forward formula from ordinary compact distribution tests. The candidate weak
PDE is produced natively, then merely restricted to compact spatial tests. -/
theorem compact_distributional_energy_literal_formula
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b))
    (hu : CompactWeakEquation a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t)))
    (t : Set.Icc a b) (φ : FreeFlow.Test) :
    energyDistribution (u t) φ =
      FreeFlow.free ((t : ℝ)-a) (energyDistribution (u a)) φ - Complex.I *
        ∫ s in Set.Ioc a (t : ℝ),
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  have he := compact_energy_weak_uniqueness hUnique hSob (Set.left_mem_Icc.mpr hab) u
    (actualRetardedCandidate hDensity hSob h0 hret hab E (u a))
    (fun t => Lp.toTemperedDistribution (E.value t)) hucont
    (actualRetardedCandidate_continuous hDensity hSob h0 hret hab E (u a)).continuousOn
    hu (actualRetardedCandidate_weakEquation hDensity hSob h0 hret hab E (u a) hgen).toCompact
    (actualRetardedCandidate_initial hDensity hSob h0 hret hab E (u a)).symm t t.property
  rw [he]
  exact actualRetardedCandidate_scalar hDensity hSob h0 hret hab E (u a) t φ

/-- The complete compact-test formula at any base time, forward or backward.
No original scalar L2 domain, mild-formula premise or candidate-PDE premise occurs. -/
theorem compact_distributional_energy_literal_formula_at
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b))
    (hu : CompactWeakEquation a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t)))
    (t₀ t : Set.Icc a b) (φ : FreeFlow.Test) :
    IntervalIntegrable (fun s => Lp.toTemperedDistribution (E.value s)
      (freeTest ((t : ℝ)-s) φ)) volume (t₀ : ℝ) (t : ℝ) ∧
    energyDistribution (u t) φ =
      FreeFlow.free ((t : ℝ)-(t₀ : ℝ)) (energyDistribution (u t₀)) φ - Complex.I *
        ∫ s in (t₀ : ℝ)..(t : ℝ),
          Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) :=
  literal_formula_restart hDensity hSob E u
    (compact_distributional_energy_literal_formula hDensity hSob h0 hret hab E
      hgen hUnique u hucont hu) t₀ t φ

/-- Actual state equality exposes the constructed representative for subsequent
endpoint bounds and continuation; it is stronger than equality of scalar tests. -/
theorem compact_energy_eq_actual_candidate
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b))
    (hu : CompactWeakEquation a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t))) (t : Set.Icc a b) :
    u t = actualRetardedCandidate hDensity hSob h0 hret hab E (u a) t := by
  apply energyDistribution_injective
  ext φ
  rw [compact_distributional_energy_literal_formula hDensity hSob h0 hret hab E
    hgen hUnique u hucont hu t φ,
    actualRetardedCandidate_scalar hDensity hSob h0 hret hab E (u a) t φ]

/-- Full equivalence with the literal original-source formula on the same actual
energy path. Reverse implication uses the produced candidate PDE and distribution
testing; it introduces no new ordinary interface. -/
theorem compact_distributional_energy_iff_literal_formula
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (u : ℝ → EnergyState) (hucont : ContinuousOn u (Set.Icc a b)) :
    CompactWeakEquation a b (fun t => energyDistribution (u t))
      (fun t => Lp.toTemperedDistribution (E.value t)) ↔
    ∀ t : Set.Icc a b, ∀ φ : FreeFlow.Test,
      energyDistribution (u t) φ =
        FreeFlow.free ((t : ℝ)-a) (energyDistribution (u a)) φ - Complex.I *
          ∫ s in Set.Ioc a (t : ℝ),
            Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ)-s) φ) := by
  constructor
  · exact compact_distributional_energy_literal_formula hDensity hSob h0 hret hab E
      hgen hUnique u hucont
  · intro hFormula
    apply (actualRetardedCandidate_weakEquation hDensity hSob h0 hret hab E (u a) hgen).toCompact.state_congr
    intro t ht
    ext φ
    rw [hFormula ⟨t, ht⟩ φ]
    exact actualRetardedCandidate_scalar hDensity hSob h0 hret hab E (u a) ⟨t, ht⟩ φ

end HartreeF.LinearWeakEquation
