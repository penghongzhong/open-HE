import FMaximalFiniteSGlobalScattering
import FActualMildToForcedCompactPDE
import FActualApproximateGlobalWBound
import FActualCompactMaximalPerturbation
import FActualBackwardCompactMaximalPerturbation

/-!
Finite-side graph stability for the original actual maximal trajectories.

The endpoint arguments precede the compact PDE and perturbation arguments:
a native pure-gradient cap and finite S on the existing domain first give the
corresponding whole half-line. Uniform graph bounds and stability are then
proved for the actual compact paths. This is an UNCOMPILED source draft.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HartreeF.BilateralSideStability
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open MaximalTrajectory SobolevStretch StationarySelfTest Retarded ActualStrichartz
open EndpointOutput ForcingDomain CriticalUniqueness CriticalSourceBounds
open HartreeDistributionalBridge LinearWeakEquation L1RetardedIndependentReview
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalGradient hartreeDuhamelMap criticalPathIntervalSource LocalMildTrajectory.path

/-- Finite forward S rules out the finite right endpoint of this maximal
trajectory. No forward-domain premise is assumed. -/
theorem forward_halfLine_subset_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (psi : EnergyState) (V : LocalMildTrajectory alpha kernel a psi)
    (hmax : V.domain = maximalDomain alpha kernel a psi)
    (hgradient : ∀ t ∈ V.domain, pureGradientNorm (V.state t) ≤ B)
    (hfiniteS : ActualScattering.FiniteSAfter V) : Set.Ici a ⊆ V.domain := by
  obtain ⟨M, hS⟩ := hfiniteS
  have hstate := MaximalFiniteSGlobal.state_cap_of_pure_gradient hSob V hgradient
  have hunbounded : ¬ BddAbove V.domain := by
    intro hbdd
    obtain ⟨haT, hV, hT⟩ := MaximalFiniteSGlobal.right_endpoint_of_bddAbove
      V.domain_open V.domain_connected V.center_mem hbdd
    apply FiniteSContinuation.maximal_finite_right_endpoint_not_finite_s
      hDensity hSob h0 hfree hret hefree heret hH psi V hmax haT hV hT
      (fun t ht => hstate t (hV ht))
    exact ⟨M, fun b hab _ hI => hS b hab hI⟩
  intro t ht
  obtain ⟨b, hb, htb⟩ := not_bddAbove_iff.mp hunbounded t
  exact V.domain_connected.out' V.center_mem hb ⟨ht, htb.le⟩

/-- Finite backward S rules out the finite left endpoint before any use of
compact backward perturbation. The PDE keeps its original time orientation. -/
theorem backward_halfLine_subset_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (psi : EnergyState) (V : LocalMildTrajectory alpha kernel a psi)
    (hmax : V.domain = maximalDomain alpha kernel a psi)
    (hgradient : ∀ t ∈ V.domain, pureGradientNorm (V.state t) ≤ B)
    (hfiniteS : ActualLeftScattering.FiniteSBefore V) : Set.Iic a ⊆ V.domain := by
  obtain ⟨M, hS⟩ := hfiniteS
  have hstate := MaximalFiniteSGlobal.state_cap_of_pure_gradient hSob V hgradient
  have hunbounded : ¬ BddBelow V.domain := by
    intro hbdd
    obtain ⟨hTa, hV, hT⟩ := MaximalFiniteSGlobal.left_endpoint_of_bddBelow
      V.domain_open V.domain_connected V.center_mem hbdd
    apply LeftFiniteSContinuation.maximal_finite_left_endpoint_not_finite_s
      hDensity hSob h0 hfree hret hefree heret hH psi V hmax hTa hV hT
      (fun t ht => hstate t (hV ht))
    exact ⟨M, fun b hba _ hI => hS b hba hI⟩
  intro t ht
  obtain ⟨b, hb, hbt⟩ := not_bddBelow_iff.mp hunbounded t
  exact V.domain_connected.out' hb V.center_mem ⟨hbt.le, ht⟩

/-- Pointwise state bounds control every actual compact energy coordinate,
including the zero-width path. -/
theorem compact_energy_norm_le_of_state_cap {alpha kernel s G : ℝ}
    {psi : EnergyState} (V : LocalMildTrajectory alpha kernel s psi)
    (hG : 0 ≤ G) (hstate : ∀ t ∈ V.domain, ‖V.state t‖ ≤ G)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ V.domain) :
    ‖energyPath (intervalMeasure a b) (V.path hab hI)‖ ≤ G := by
  apply (ContinuousMap.norm_le _ hG).mpr
  intro t
  rw [V.path_agrees]
  exact hstate t (hI t.property)

/-- Energy-topology convergence to a native finite-forward-S datum gives one
uniform graph bound for every nonnegative compact prefix of all sufficiently
late original-data actual maximal trajectories. Their half-line domains are
outputs, and all choices of compact-path membership proof are covered. -/
theorem exists_eventual_forward_graph_cap_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (psi : EnergyState) (hB : 0 ≤ B)
    (hgradient : ∀ t ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).domain,
      pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).state t) ≤ B)
    (hfiniteS : ActualScattering.FiniteSAfter
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi))
    (z : ℕ → EnergyState) (hz : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N,
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n)
      Set.Ici 0 ⊆ U.domain ∧
        ∀ (b : ℝ) (hb : 0 ≤ b) (hI : Set.Icc 0 b ⊆ U.domain), ‖U.path hb hI‖ ≤ R := by
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi
  have hV : Set.Ici 0 ⊆ V.domain := forward_halfLine_subset_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH psi V rfl hgradient hfiniteS
  obtain ⟨M, hS⟩ := hfiniteS
  let A : ℝ := max (K ^ ((6 : ℝ)⁻¹)) 1 * B
  have hA : 0 ≤ A := mul_nonneg
    (le_trans zero_le_one (le_max_right _ _)) hB
  have hstate : ∀ t ∈ V.domain, ‖V.state t‖ ≤ A :=
    MaximalFiniteSGlobal.state_cap_of_pure_gradient hSob V hgradient
  have hVI (b : ℝ) (_hb : 0 ≤ b) : Set.Icc 0 b ⊆ V.domain :=
    fun _ ht => hV ht.1
  have henergy (b : ℝ) (hb : 0 ≤ b) :
      ‖energyPath (intervalMeasure 0 b) (V.path hb (hVI b hb))‖ ≤ A :=
    compact_energy_norm_le_of_state_cap V hA hstate hb (hVI b hb)
  have hsize (b : ℝ) (hb : 0 ≤ b) :
      pathValueSize (intervalMeasure 0 b) (V.path hb (hVI b hb)) ≤
        ENNReal.ofReal (M : ℝ) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hS b hb (hVI b hb)
  have hpde (b : ℝ) (hb : 0 ≤ b) :
      ForcedHartreeCompactTestIdentity alpha kernel hb (V.path hb (hVI b hb))
        (zeroSource 0 b) :=
    HartreeMildPDEProducer.actual_zero_compactPDE_of_original_mild
      hDensity hSob hH h0 hfree hret hb (V.path hb (hVI b hb)) (V.state 0)
      hgen (V.path_mild hb (hVI b hb))
  obtain ⟨L, hL, hgraph⟩ :=
    ApproximateGlobalW.exists_uniform_graph_bound_of_actual_PDE_energy_S
      hDensity hSob h0 hfree hret hH hgen hUnique hA M.coe_nonneg
  have href (b : ℝ) (hb : 0 ≤ b) : ‖V.path hb (hVI b hb)‖ ≤ L := by
    apply hgraph hb (V.path hb (hVI b hb)) (zeroSource 0 b)
      (hpde b hb) (henergy b hb) (hsize b hb)
    simp only [zeroSource, norm_zero]
    norm_num
  obtain ⟨epsilon0, C, hepsilon0, _hepsilon1, hC, hperturb⟩ :=
    CompactLongTimePerturbation.exists_actual_maximal_compact_perturbation
      hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hA M.coe_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hz.eventually (Iio_mem_nhds hepsilon0))
  refine ⟨C * epsilon0 + L, add_nonneg (mul_nonneg hC.le hepsilon0.le) hL, N, ?_⟩
  intro n hn
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n)
  have hcompact (b : ℝ) (hb : 0 ≤ b) :
      ∃ hI : Set.Icc 0 b ⊆ U.domain,
        ‖U.path hb hI - V.path hb (hVI b hb)‖ ≤ C * epsilon0 := by
    have hinit : ‖z n - energyPath _ (V.path hb (hVI b hb)) ⟨0, le_rfl, hb⟩‖ ≤
        epsilon0 := by
      simpa only [V.path_agrees, V.initial] using (hN n hn).le
    have herr : ‖(zeroSource 0 b).gradient‖ ≤ epsilon0 := by
      simpa only [zeroSource, norm_zero] using hepsilon0.le
    obtain ⟨hI, hresult⟩ := hperturb hb (z n) (V.path hb (hVI b hb))
      (zeroSource 0 b) (hpde b hb) (henergy b hb) (hsize b hb)
      hepsilon0.le le_rfl hinit herr
    exact ⟨hI, hresult.2.2.2.2.1⟩
  constructor
  · intro t ht
    obtain ⟨hI, _⟩ := hcompact t ht
    exact hI ⟨ht, le_rfl⟩
  · intro b hb hI
    have hclose' : ‖U.path hb hI - V.path hb (hVI b hb)‖ ≤ C * epsilon0 :=
      (hcompact b hb).choose_spec
    exact (norm_le_norm_add_norm_sub' (U.path hb hI) (V.path hb (hVI b hb))).trans
      ((add_le_add (href b hb) hclose').trans_eq (add_comm _ _))

/-- The terminal-data analogue gives all actual compact prefixes of the
negative half-line, using literal backward compact perturbation after native
left-endpoint continuation. No time-reversed solution is introduced. -/
theorem exists_eventual_backward_graph_cap_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (psi : EnergyState) (hB : 0 ≤ B)
    (hgradient : ∀ t ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).domain,
      pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).state t) ≤ B)
    (hfiniteS : ActualLeftScattering.FiniteSBefore
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi))
    (z : ℕ → EnergyState) (hz : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N,
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n)
      Set.Iic 0 ⊆ U.domain ∧
        ∀ (a : ℝ) (ha : a ≤ 0) (hI : Set.Icc a 0 ⊆ U.domain), ‖U.path ha hI‖ ≤ R := by
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi
  have hV : Set.Iic 0 ⊆ V.domain := backward_halfLine_subset_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH psi V rfl hgradient hfiniteS
  obtain ⟨M, hS⟩ := hfiniteS
  let A : ℝ := max (K ^ ((6 : ℝ)⁻¹)) 1 * B
  have hA : 0 ≤ A := mul_nonneg
    (le_trans zero_le_one (le_max_right _ _)) hB
  have hstate : ∀ t ∈ V.domain, ‖V.state t‖ ≤ A :=
    MaximalFiniteSGlobal.state_cap_of_pure_gradient hSob V hgradient
  have hVI (a : ℝ) (_ha : a ≤ 0) : Set.Icc a 0 ⊆ V.domain :=
    fun _ ht => hV ht.2
  have henergy (a : ℝ) (ha : a ≤ 0) :
      ‖energyPath (intervalMeasure a 0) (V.path ha (hVI a ha))‖ ≤ A :=
    compact_energy_norm_le_of_state_cap V hA hstate ha (hVI a ha)
  have hsize (a : ℝ) (ha : a ≤ 0) :
      pathValueSize (intervalMeasure a 0) (V.path ha (hVI a ha)) ≤
        ENNReal.ofReal (M : ℝ) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hS a ha (hVI a ha)
  have hpde (a : ℝ) (ha : a ≤ 0) :
      ForcedHartreeCompactTestIdentity alpha kernel ha (V.path ha (hVI a ha))
        (zeroSource a 0) :=
    HartreeMildPDEProducer.actual_zero_compactPDE_of_original_mild
      hDensity hSob hH h0 hfree hret ha (V.path ha (hVI a ha)) (V.state a)
      hgen (V.path_mild ha (hVI a ha))
  obtain ⟨L, hL, hgraph⟩ :=
    ApproximateGlobalW.exists_uniform_graph_bound_of_actual_PDE_energy_S
      hDensity hSob h0 hfree hret hH hgen hUnique hA M.coe_nonneg
  have href (a : ℝ) (ha : a ≤ 0) : ‖V.path ha (hVI a ha)‖ ≤ L := by
    apply hgraph ha (V.path ha (hVI a ha)) (zeroSource a 0)
      (hpde a ha) (henergy a ha) (hsize a ha)
    simp only [zeroSource, norm_zero]
    norm_num
  obtain ⟨epsilon0, C, hepsilon0, _hepsilon1, hC, hperturb⟩ :=
    BackwardCompactLongTimePerturbation.exists_actual_maximal_backward_compact_perturbation
      hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hA M.coe_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hz.eventually (Iio_mem_nhds hepsilon0))
  refine ⟨C * epsilon0 + L, add_nonneg (mul_nonneg hC.le hepsilon0.le) hL, N, ?_⟩
  intro n hn
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n)
  have hcompact (a : ℝ) (ha : a ≤ 0) :
      ∃ hI : Set.Icc a 0 ⊆ U.domain,
        ‖U.path ha hI - V.path ha (hVI a ha)‖ ≤ C * epsilon0 := by
    have hinit : ‖z n - energyPath _ (V.path ha (hVI a ha)) ⟨0, ha, le_rfl⟩‖ ≤
        epsilon0 := by
      simpa only [V.path_agrees, V.initial] using (hN n hn).le
    have herr : ‖(zeroSource a 0).gradient‖ ≤ epsilon0 := by
      simpa only [zeroSource, norm_zero] using hepsilon0.le
    obtain ⟨hI, hresult⟩ := hperturb ha (z n) (V.path ha (hVI a ha))
      (zeroSource a 0) (hpde a ha) (henergy a ha) (hsize a ha)
      hepsilon0.le le_rfl hinit herr
    exact ⟨hI, hresult.2.2.2.2.1⟩
  constructor
  · intro t ht
    obtain ⟨hI, _⟩ := hcompact t ht
    exact hI ⟨le_rfl, ht⟩
  · intro a ha hI
    have hclose' : ‖U.path ha hI - V.path ha (hVI a ha)‖ ≤ C * epsilon0 :=
      (hcompact a ha).choose_spec
    exact (norm_le_norm_add_norm_sub' (U.path ha hI) (V.path ha (hVI a ha))).trans
      ((add_le_add (href a ha) hclose').trans_eq (add_comm _ _))

end HartreeF.BilateralSideStability
