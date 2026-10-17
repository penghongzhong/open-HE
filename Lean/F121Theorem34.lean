import F121LiteralSolutionClass
import FActualGlobalIntervalStability
import FActualMildToForcedCompactPDE
import FCompactUniformCenteredLifespanNative
import FLocalMildFiniteDuhamel
import FPaperStabilitySumNorm
import FActualEuclideanForcingNorm
import FActualSIntervalBounds
import FActualBilateralPathTools

/-! Literal terminal wrapper for Theorem 3.4 of the 121-page manuscript.
The canonical maximal trajectory is compared with every literal solution, its
same actual restrictions carry E/W/Z/S, and perturbations are measured on the
actual complex gradient and value fields on every compact lifespan window. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Interval
namespace HartreeF.Paper121Theorem34
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput
open ForcingDomain CriticalUniqueness MaximalTrajectory Paper121LiteralClass
open OriginalSignedDuhamel TimeHolder CriticalSourceBounds HomogeneousStability
open PaperNormCompactPerturbation IntervalNormExhaustion IntervalPerturbation
open CompactUniformLifespan BilateralPathTools ActualSIntervalBounds
open HartreeMildPDEProducer LinearWeakEquation HartreeDistributionalBridge
open L1RetardedIndependentReview CriticalPathRestriction

/-- The four literal compact path quantities E, W, Z and S, all evaluated on
the same actual complex gradient/value representatives. -/
def FourFinitePathQuantities {a b : ℝ}
    (u : CriticalPath (intervalMeasure a b)) : Prop :=
  mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ u t)) ≠ ∞ ∧
  mixedNorm (intervalMeasure a b) volume 10 criticalExponent
      (fun t => energyComplexGradient (energyPath _ u t)) ≠ ∞ ∧
  mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyComplexGradient (energyPath _ u t)) ≠ ∞ ∧
  mixedNorm (intervalMeasure a b) volume 10 10
      (fun t => energyValue (energyPath _ u t)) ≠ ∞

theorem fourFinitePathQuantities
    (hDensity : OrdinaryH1Density) {K a b : ℝ} (hSob : OrdinarySobolev K)
    (u : CriticalPath (intervalMeasure a b)) (hu : FullZPath u) :
    FourFinitePathQuantities u := by
  have hE := actual_complex_energy_le_sqrt_three_graph u
  have hW := actual_complex_W_le_three_graph u
  obtain ⟨W⟩ := hu
  have hsum : (∑ j : Fin 3, mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ u t))) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun j _ => W.mixedNorm_finite j)
  have hZ := criticalPath_complex_endpoint_le_sum u
  have hS := pathValueSize_le_graph hDensity hSob u
  unfold FourFinitePathQuantities
  refine ⟨ne_top_of_le_ne_top (by finiteness) hE,
    ne_top_of_le_ne_top (by finiteness) hW,
    ne_top_of_le_ne_top hsum hZ, ?_⟩
  rw [← pathValueSize_eq_actual_S]
  exact ne_top_of_le_ne_top (by finiteness) hS

/-- Both time orientations of the actual Hartree Duhamel formula, together
with absolute convergence of the displayed tested finite integrals. -/
def ActualHartreeDuhamelOnDomain {alpha kernel s0 : ℝ} {u0 : EnergyState}
    (M : LocalMildTrajectory alpha kernel s0 u0) : Prop :=
  ∀ {a b : ℝ} (_hab : a ≤ b) (_hI : Icc a b ⊆ M.domain) (φ : FreeFlow.Test),
    IntegrableOn (fun z => ∫ x,
      freeTest (b-z) φ x * forcing alpha kernel (energyValue (M.state z)) x)
      (Icc a b) volume ∧
    IntegrableOn (fun z => ∫ x,
      freeTest (a-z) φ x * forcing alpha kernel (energyValue (M.state z)) x)
      (Icc a b) volume ∧
    energyDistribution (M.state b) φ =
      energyDistribution (M.state a) (freeTest (b-a) φ) + Complex.I *
        ∫ z in Icc a b, ∫ x,
          freeTest (b-z) φ x * forcing alpha kernel (energyValue (M.state z)) x ∧
    energyDistribution (M.state a) φ =
      energyDistribution (M.state b) (freeTest (a-b) φ) - Complex.I *
        ∫ z in Icc a b, ∫ x,
          freeTest (a-z) φ x * forcing alpha kernel (energyValue (M.state z)) x

theorem actualHartreeDuhamelOnDomain
    (hDensity : OrdinaryH1Density) {K alpha kernel s0 : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (M : LocalMildTrajectory alpha kernel s0 u0) :
    ActualHartreeDuhamelOnDomain M := by
  intro a b hab hI φ
  exact ⟨local_freeTest_source_integrable M hDensity hSob hH hab hI b φ,
    local_freeTest_source_integrable M hDensity hSob hH hab hI a φ,
    local_mild_forward_original M hab hI φ,
    local_mild_terminal_positive M hab hI φ⟩

theorem actualPaperDifferenceSize_mono {I J : Set ℝ} {u q : ℝ → EnergyState}
    (hJI : J ⊆ I) :
    actualPaperDifferenceSize J u q ≤ actualPaperDifferenceSize I u q := by
  have hμ : volume.restrict J ≤ volume.restrict I :=
    Measure.restrict_mono_set volume hJI
  unfold actualPaperDifferenceSize mixedNorm
  exact add_le_add (add_le_add (add_le_add
    (eLpNorm_mono_measure _ hμ) (eLpNorm_mono_measure _ hμ))
    (eLpNorm_mono_measure _ hμ)) (eLpNorm_mono_measure _ hμ)

/-- Locally Lipschitz dependence in C_t X and simultaneously in the literal
sum E+W+Z+S on every compact subinterval of the reference lifespan. -/
def CompactFlowDependence
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s0 : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (u0 : EnergyState)
    (M : LocalMildTrajectory alpha kernel s0 u0) : Prop :=
  ∀ {a b : ℝ} (_hab : a ≤ b), Icc a b ⊆ M.domain →
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ f : EnergyState, ‖f-u0‖ ≤ delta →
        let U := actualMaximalTrajectory hDensity hSob h0 hfree hret
          hefree heret hH s0 f
        Icc a b ⊆ U.domain ∧
        actualPaperDifferenceSize (Icc a b) U.state M.state ≤
          ENNReal.ofReal (C*‖f-u0‖) ∧
        ∀ t ∈ Icc a b, ‖U.state t-M.state t‖ ≤ C*‖f-u0‖

theorem compactFlowDependence
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s0 : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (u0 : EnergyState)
    (M : LocalMildTrajectory alpha kernel s0 u0) (hM0 : M.state s0 = u0) :
    CompactFlowDependence hDensity hSob h0 hfree hret hefree heret hH u0 M := by
  intro a b hab hI
  let A := min a s0
  let B := max b s0
  have haM : a ∈ M.domain := hI ⟨le_rfl, hab⟩
  have hbM : b ∈ M.domain := hI ⟨hab, le_rfl⟩
  have hAM : A ∈ M.domain := by
    by_cases h : a ≤ s0
    · simpa only [A, min_eq_left h] using haM
    · simpa only [A, min_eq_right (le_of_not_ge h)] using M.center_mem
  have hBM : B ∈ M.domain := by
    by_cases h : b ≤ s0
    · simpa only [B, max_eq_right h] using M.center_mem
    · simpa only [B, max_eq_left (le_of_not_ge h)] using hbM
  have hAB : A ≤ B := (min_le_right a s0).trans (le_max_right b s0)
  have hHull : Icc A B ⊆ M.domain := M.domain_connected.out' hAM hBM
  have hsHull : s0 ∈ Icc A B := ⟨min_le_right _ _, le_max_right _ _⟩
  have hcompact : Icc a b ⊆ Icc A B := by
    intro t ht
    exact ⟨(min_le_left _ _).trans ht.1, ht.2.trans (le_max_left _ _)⟩
  let q := M.path hAB hHull
  let graphS : ℝ := graphSConstant K * ‖q‖
  obtain ⟨epsilon0, C, hepsilon0, _hepsilon1, hC, hstable⟩ :=
    exists_actual_global_interval_stability
      (B := ‖energyPath (intervalMeasure A B) q‖) (M := graphS)
      hDensity hSob h0 hfree hret hefree heret hH hgen hUnique
      (norm_nonneg (energyPath (intervalMeasure A B) q))
      (mul_nonneg (graphSConstant_nonneg hSob) (norm_nonneg q))
  let L : ℝ := max (K ^ ((6 : ℝ)⁻¹)) 1
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  refine ⟨epsilon0, L*C, hepsilon0, mul_pos hL0 hC, ?_⟩
  intro f hf
  let Q : ∀ {c d : ℝ}, c ≤ d → Icc c d ⊆ Icc A B →
      CriticalPath (intervalMeasure c d) :=
    fun hcd hsub => M.path hcd (hsub.trans hHull)
  let E : ∀ {c d : ℝ}, c ≤ d → Icc c d ⊆ Icc A B →
      CompatibleL1IntervalSource c d := fun _ _ => zeroSource _ _
  have hQ : ∀ {c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc A B)
      (t : Icc c d), energyPath _ (Q hcd hsub) t = M.state t := by
    intro c d hcd hsub t
    exact M.path_agrees hcd (hsub.trans hHull) t
  have hPDE : ∀ {c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc A B),
      ForcedHartreeCompactTestIdentity alpha kernel hcd (Q hcd hsub) (E hcd hsub) := by
    intro c d hcd hsub
    exact actual_zero_compactPDE_of_original_mild hDensity hSob hH h0 hfree hret
      hcd (Q hcd hsub) (M.state c) hgen (M.path_mild hcd (hsub.trans hHull))
  have hEnergy : ∀ {c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc A B),
      ‖energyPath _ (Q hcd hsub)‖ ≤ ‖energyPath (intervalMeasure A B) q‖ := by
    intro c d hcd hsub
    have hc := hsub ⟨le_rfl, hcd⟩
    have hd := hsub ⟨hcd, le_rfl⟩
    rw [show Q hcd hsub = restrictPath hc.1 hcd hd.2 q from
      path_restrict M hAB hHull hc.1 hcd hd.2 (hsub.trans hHull)]
    exact restrictPath_energy_norm_le hc.1 hcd hd.2 q
  have hS : ∀ {c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc A B),
      pathValueSize (intervalMeasure c d) (Q hcd hsub) ≤ ENNReal.ofReal graphS := by
    intro c d hcd hsub
    have hc := hsub ⟨le_rfl, hcd⟩
    have hd := hsub ⟨hcd, le_rfl⟩
    exact (actual_snorm_mono hDensity hSob M hAB hHull hc.1 hcd hd.2
      (hsub.trans hHull)).trans (pathValueSize_le_graph hDensity hSob q)
  have hErr : ∀ {c d : ℝ} (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc A B),
      ‖(E hcd hsub).gradient‖ ≤ ‖f-u0‖ := by
    intro c d hcd hsub
    simpa only [E, zeroSource, norm_zero] using norm_nonneg (f-u0)
  have hInitial : ‖f-M.state s0‖ ≤ ‖f-u0‖ := by
    simpa only [hM0] using (le_refl ‖f-u0‖)
  have hglobal := hstable (Icc A B) ordConnected_Icc hsHull f M.state Q E hQ hPDE
    hEnergy hS hErr (norm_nonneg _) hf hInitial
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 f
  have hCscale : C ≤ L*C := by
    calc
      C = 1*C := (one_mul C).symm
      _ ≤ L*C := mul_le_mul_of_nonneg_right hL1 hC.le
  have hscale : C*‖f-u0‖ ≤ (L*C)*‖f-u0‖ := by
    exact mul_le_mul_of_nonneg_right hCscale (norm_nonneg (f-u0))
  refine ⟨hcompact.trans hglobal.1,
    (actualPaperDifferenceSize_mono hcompact).trans
      (hglobal.2.2.1.trans (ENNReal.ofReal_le_ofReal hscale)), ?_⟩
  intro t ht
  exact (energyState_le_pureGradient hSob (U.state t-M.state t)).trans
    ((mul_le_mul_of_nonneg_left (hglobal.2.2.2 t (hcompact ht)) hL0.le).trans_eq (by ring))

/-- The actual maximal local flow, including literal maximality, actual
finite-time Duhamel identities, all four finite path quantities, compact-flow
dependence and a uniform centered lifespan for compact sets of data. -/
theorem theorem34_actual_maximal_local_flow
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) :
    (∀ (s0 : ℝ) (u0 : EnergyState),
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret
        hefree heret hH s0 u0
      M.domain = maximalDomain alpha kernel s0 u0 ∧
      IsOpen M.domain ∧ OrdConnected M.domain ∧ s0 ∈ M.domain ∧ M.state s0 = u0 ∧
      ActualHartreeDuhamelOnDomain M ∧
      (∀ V : LiteralLocalSolution alpha kernel s0 u0,
        V.domain ⊆ M.domain ∧ EqOn M.state V.state V.domain ∧
          (M.domain ⊆ V.domain →
            V.domain = M.domain ∧ EqOn V.state M.state M.domain)) ∧
      (∀ {a b : ℝ} (hab : a ≤ b) (_hI : Icc a b ⊆ M.domain),
        ∃ u : CriticalPath (intervalMeasure a b),
          (∀ t : Icc a b, energyPath _ u t = M.state t) ∧
          IsMildHartreePath hab alpha kernel (M.state a) u ∧
          FullZPath u ∧ FourFinitePathQuantities u) ∧
      CompactFlowDependence hDensity hSob h0 hfree hret hefree heret hH u0 M) ∧
    (∀ Q : Set EnergyState, IsCompact Q →
      ∃ delta : ℝ, 0 < delta ∧ ∀ q ∈ Q,
        Icc (-delta) delta ⊆
          (actualMaximalTrajectory hDensity hSob h0 hfree hret
            hefree heret hH 0 q).domain) := by
  constructor
  · intro s0 u0
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret
      hefree heret hH s0 u0
    refine ⟨rfl, M.domain_open, M.domain_connected, M.center_mem, M.initial,
      actualHartreeDuhamelOnDomain hDensity hSob hH M,
      ?_, ?_, compactFlowDependence hDensity hSob h0 hfree hret hefree heret
        hH hgen hUnique u0 M M.initial⟩
    · intro V
      exact actual_maximal_among_literal_solutions hDensity hSob h0 hfree hret
        hefree heret hH s0 u0 V
    · intro a b hab hI
      let u := M.path hab hI
      have huZ := LocalMildTrajectory.path_fullZ hDensity hSob h0 hfree hret
        hefree heret hH M hab hI
      exact ⟨u, M.path_agrees hab hI, M.path_mild hab hI, huZ,
        fourFinitePathQuantities hDensity hSob u huZ⟩
  · intro Q hQ
    obtain ⟨delta, hdelta, hlocal⟩ :=
      exists_compact_uniform_centered_lifespan hDensity hSob h0 hfree hret hH hQ
    refine ⟨delta, hdelta, ?_⟩
    intro q hq
    obtain ⟨U, hU⟩ := hlocal q hq
    exact hU.trans (subset_maximalDomain U)

end HartreeF.Paper121Theorem34
