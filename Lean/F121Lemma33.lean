import FL1AdvancedIdentification
import FL1AdvancedEndpointWitness
import FActualPDEToDuhamelRestart
import FEndpointComplexVectorDifference

/-! Literal terminal wrapper for Lemma 3.3 of the 121-page manuscript.
The source value is genuinely time-L1, its displayed spatial derivatives are
genuinely time-L2, and the same representatives enter both the constructed
retarded/advanced paths and the tested PDE--Duhamel equivalence. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Interval
namespace HartreeF.Paper121Lemma33
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput
open LinearWeakEquation FreeTestBounds TimeHolder

def RawRetardedFormula {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (u : CriticalPath (intervalMeasure a b)) : Prop :=
  ∀ t : Icc a b, ∀ φ : FreeFlow.Test,
    energyDistribution (energyPath _ u t) φ =
      ∫ s in Ioc a (t : ℝ),
        Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ) - s) φ)

def RawAdvancedFormula {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (u : CriticalPath (intervalMeasure a b)) : Prop :=
  ∀ t : Icc a b, ∀ φ : FreeFlow.Test,
    energyDistribution (energyPath _ u t) φ =
      ∫ s in Ioc (t : ℝ) b,
        Lp.toTemperedDistribution (E.value s) (freeTest ((t : ℝ) - s) φ)

def ForcedFiniteDuhamel {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (u : ℝ → EnergyState) : Prop :=
  ∀ s t : Icc a b, ∀ φ : FreeFlow.Test,
    IntervalIntegrable (fun τ => Lp.toTemperedDistribution (E.value τ)
      (freeTest ((t : ℝ) - τ) φ)) volume (s : ℝ) (t : ℝ) ∧
    energyDistribution (u t) φ =
      FreeFlow.free ((t : ℝ) - (s : ℝ)) (energyDistribution (u s)) φ - Complex.I *
        ∫ τ in (s : ℝ)..(t : ℝ),
          Lp.toTemperedDistribution (E.value τ) (freeTest ((t : ℝ) - τ) φ)

def RetardedRealization
    (_hDensity : OrdinaryH1Density) {K C0 Cr Cre a b : ℝ}
    (_hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (_hret : OrdinaryRetardedStrichartz h0 Cr)
    (_heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hab : a ≤ b) (E : CompatibleL1IntervalSource a b)
    (u : CriticalPath (intervalMeasure a b)) : Prop :=
  RawRetardedFormula E u ∧
  energyPath _ u ⟨a, le_rfl, hab⟩ = 0 ∧
  ‖u‖ ≤ max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ ∧
  FullZPath u ∧
  mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ u t)) ≤
    ∑ j : Fin 3, ENNReal.ofReal (Cre * ‖E.gradient j‖)

def AdvancedRealization
    (_hDensity : OrdinaryH1Density) {K C0 Ch Cr Che Cre a b : ℝ}
    (_hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (_hfree : OrdinaryHomogeneousStrichartz Ch)
    (_hret : OrdinaryRetardedStrichartz h0 Cr)
    (_hefree : OrdinaryHomogeneousEndpointOutput Che)
    (_heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hab : a ≤ b) (E : CompatibleL1IntervalSource a b)
    (u : CriticalPath (intervalMeasure a b)) : Prop :=
  RawAdvancedFormula E u ∧
  energyPath _ u ⟨b, hab, le_rfl⟩ = 0 ∧
  ‖u‖ ≤ max (energyEndpointConstant K C0) (Ch * C0 + Cr) * ‖E.gradient‖ ∧
  FullZPath u ∧
  mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ u t)) ≤
    ∑ j : Fin 3, ENNReal.ofReal ((Che * C0 + Cre) * ‖E.gradient j‖)

private theorem weakEquation_state_congr {a b : ℝ} {U V F : ℝ → FreeFlow.TD}
    (h : WeakEquation a b U F) (hUV : ∀ t ∈ Icc a b, U t = V t) :
    WeakEquation a b V F := by
  intro η hη φ
  obtain ⟨hUi, hFi, he⟩ := h η hη φ
  have hae : weakOperator U η φ =ᵐ[volume.restrict (Icc a b)] weakOperator V η φ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [weakOperator, hUV t ht]
  exact ⟨hUi.congr hae, hFi, (integral_congr_ae hae).symm.trans he⟩

private theorem retarded_unique {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (u v : CriticalPath (intervalMeasure a b))
    (hu : RawRetardedFormula E u) (hv : RawRetardedFormula E v) : u = v := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  apply ContinuousLinearMap.ext
  intro φ
  exact (hu t φ).trans (hv t φ).symm

private theorem advanced_unique {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (u v : CriticalPath (intervalMeasure a b))
    (hu : RawAdvancedFormula E u) (hv : RawAdvancedFormula E v) : u = v := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  apply ContinuousLinearMap.ext
  intro φ
  exact (hu t φ).trans (hv t φ).symm

/-- Full Lemma 3.3: unique actual retarded and terminal realizations, their
graph/endpoint estimates, absolute finite tested integrals, and both directions
of the tested PDE--finite-Duhamel equivalence. -/
theorem lemma33_compatible_sources_and_literal_finite_duhamel
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2HomogeneousUniqueness) :
    ∀ {a b : ℝ} (hab : a ≤ b) (E : CompatibleL1IntervalSource a b),
      (∃! u : CriticalPath (intervalMeasure a b),
        RetardedRealization hDensity hSob h0 hret heret hab E u) ∧
      (∃! u : CriticalPath (intervalMeasure a b),
        AdvancedRealization hDensity hSob h0 hfree hret hefree heret hab E u) ∧
      ∀ u : ℝ → EnergyState, ContinuousOn u (Icc a b) →
        (WeakEquation a b (fun t => energyDistribution (u t))
          (fun t => Lp.toTemperedDistribution (E.value t)) ↔
        ForcedFiniteDuhamel E u) := by
  intro a b hab E
  let r := E.retardedCriticalPath hDensity hSob h0 hret
  let q := E.advancedCriticalPath hDensity hSob h0 hfree hret
  have hrFormula : RawRetardedFormula E r := by
    intro t φ
    exact E.retardedCriticalPath_forward_scalar hDensity hSob h0 hret t φ
  have hqFormula : RawAdvancedFormula E q := by
    intro t φ
    exact E.advancedCriticalPath_scalar hDensity hSob h0 hfree hret t φ
  have hrZ : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ r t)) ≤
      ∑ j : Fin 3, ENNReal.ofReal (Cre * ‖E.gradient j‖) := by
    exact (criticalPath_complex_endpoint_le_sum r).trans
      (Finset.sum_le_sum fun j _ =>
        l1RetardedCriticalPath_endpoint_bound hDensity hSob h0 hret heret E j)
  have hqZ : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ q t)) ≤
      ∑ j : Fin 3, ENNReal.ofReal ((Che * C0 + Cre) * ‖E.gradient j‖) := by
    let W := E.advancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret
      hefree heret hab
    exact (criticalPath_complex_endpoint_le_sum q).trans
      (Finset.sum_le_sum fun j _ => (W.mixedNorm_eq j).le.trans
        (E.advancedCriticalPath_endpoint_enorm_bound hDensity hSob h0 hfree hret
          hefree heret hab j))
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨r, ⟨hrFormula,
      E.retardedCriticalPath_initial hDensity hSob h0 hret hab,
      E.retardedCriticalPath_norm_le hDensity hSob h0 hret,
      l1RetardedCriticalPath_fullZ hDensity hSob h0 hret heret E, hrZ⟩, ?_⟩
    intro v hv
    exact retarded_unique E v r hv.1 hrFormula
  · refine ⟨q, ⟨hqFormula,
      E.advancedCriticalPath_terminal hDensity hSob h0 hfree hret hab,
      E.advancedCriticalPath_norm_le hDensity hSob h0 hfree hret,
      ⟨E.advancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret
        hefree heret hab⟩, hqZ⟩, ?_⟩
    intro v hv
    exact advanced_unique E v q hv.1 hqFormula
  · intro u hucont
    constructor
    · intro hu s t φ
      exact distributional_energy_literal_formula_at hDensity hSob h0 hret hab E
        hgen hUnique u hucont hu s t φ
    · intro hFormula
      let A := actualRetardedCandidate hDensity hSob h0 hret hab E (u a)
      have hA : WeakEquation a b (fun t => energyDistribution (A t))
          (fun t => Lp.toTemperedDistribution (E.value t)) :=
        actualRetardedCandidate_weakEquation hDensity hSob h0 hret hab E (u a) hgen
      apply weakEquation_state_congr hA
      intro t ht
      apply ContinuousLinearMap.ext
      intro φ
      have hu := (hFormula ⟨a, le_rfl, hab⟩ ⟨t, ht⟩ φ).2
      have hAc := actualRetardedCandidate_scalar hDensity hSob h0 hret hab E (u a)
        ⟨t, ht⟩ φ
      rw [← intervalIntegral.integral_of_le ht.1] at hAc
      exact hAc.trans hu.symm

end HartreeF.Paper121Lemma33
