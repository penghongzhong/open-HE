import FActualLeftFiniteSTail
import FActualLeftFiniteEndpointClosure
import FClosedBackwardPathMaximalExtension
import FEnergyGradientNorm

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace HartreeF.LeftFiniteSContinuation
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded ForcingDomain CriticalUniqueness MaximalTrajectory EndpointOutput
open SobolevStretch StationarySelfTest ActualStrichartz CriticalSourceBounds ActualSTail ActualLeftSTail
open FiniteEndpoint SmallSGraphBound
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution criticalPathIntervalSource hartreeDuhamelMap

/-- Genuine finite actual compact S on all terminal segments approaching the
left endpoint. There is no source, W, small-tail or limiting-state input. -/
def FiniteSAfter {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) (T : ℝ) : Prop :=
  ∃ M : ℝ≥0, ActualLeftSTail.UniformSNormAfter U T a M

/-- A state cap controls the compact continuous energy coordinate, including
zero-width subintervals. -/
theorem compact_energy_coordinate_bound {alpha kernel a T B : ℝ}
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hB : 0 ≤ B) (hbound : ∀ t ∈ Set.Ioc T a, ‖U.state t‖ ≤ B)
    {b c : ℝ} (hTb : T < b) (hbc : b ≤ c) (hca : c ≤ a)
    (hI : Set.Icc b c ⊆ U.domain) :
    ‖energyPath (intervalMeasure b c) (U.path hbc hI)‖ ≤ B := by
  apply (ContinuousMap.norm_le _ hB).mpr
  intro t
  rw [U.path_agrees]
  exact hbound t ⟨hTb.trans_le t.property.1, t.property.2.trans hca⟩

/-- The small-S threshold is selected before the terminal restart. All
compact forward mild paths in the left tail satisfy the same graph bound;
their actual initial states are bounded by the given state cap. -/
theorem exists_threshold_uniform_critical_norm_on_left_tail (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hB : 0 ≤ B) (hbound : ∀ t ∈ Set.Ioc T a, ‖U.state t‖ ≤ B) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ (c : ℝ) (_hca : c ≤ a),
      (∀ (b : ℝ) (hbc : b ≤ c), T < b → ∀ hI : Set.Icc b c ⊆ U.domain,
        pathValueSize (intervalMeasure b c) (U.path hbc hI) ≤ ENNReal.ofReal eta) →
      UniformCriticalNormAfter U T c
        (2 * max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * B) := by
  obtain ⟨eta, heta, heta1, hgraph⟩ :=
    exists_small_s_energy_coordinate_graph_bound hDensity hSob h0 hfree hret hH hB
  refine ⟨eta, heta, heta1, ?_⟩
  intro c hca hsmall b hbc hTb hI
  have hgraph' := hgraph hbc (U.state b) (U.path hbc hI) (U.path_mild hbc hI)
    (compact_energy_coordinate_bound U hB hbound hTb hbc hca hI)
    (hsmall b hbc hTb hI)
  have hC : 0 ≤ 2 * max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch := by
    have hK : 0 ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 := le_trans zero_le_one (le_max_right _ _)
    exact mul_nonneg (by norm_num) ((mul_nonneg hK (Real.sqrt_nonneg 3)).trans (le_max_left _ _))
  exact hgraph'.trans (mul_le_mul_of_nonneg_left
    (hbound b ⟨hTb, hbc.trans hca⟩) hC)

/-- Finite actual S and a bounded actual state produce a strict extension of
the original trajectory across its excluded finite left endpoint. The new
endpoint state is constructed by the advanced compatible-source path. -/
theorem exists_strict_extension_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hTa : T < a) (hU : Set.Ioc T a ⊆ U.domain) (hT : T ∉ U.domain)
    (hbound : ∀ t ∈ Set.Ioc T a, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSAfter U T) :
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊂ V.domain ∧ T ∈ V.domain ∧ Set.EqOn V.state U.state U.domain := by
  obtain ⟨M, hS⟩ := hfiniteS
  have hB : 0 ≤ B := (norm_nonneg (U.state a)).trans (hbound a ⟨hTa, le_rfl⟩)
  obtain ⟨eta, heta, _, hgraph⟩ := exists_threshold_uniform_critical_norm_on_left_tail
    hDensity hSob h0 hfree hret hH u0 U hB hbound
  obtain ⟨c, hTc, hca, hsmall⟩ :=
    exists_uniform_small_s_left_tail hDensity hSob U hTa hU M hS heta
  have hc : c ∈ U.domain := hU ⟨hTc, hca.le⟩
  have htail : Set.Ioc T c ⊆ U.domain := by
    intro t ht
    exact hU ⟨ht.1, ht.2.trans hca.le⟩
  obtain ⟨w, _, hm⟩ := exists_closed_backward_mild_of_uniform_critical_norm
    hDensity hSob h0 hfree hret hH u0 U hTc htail
      (hgraph c hca.le fun b hbc hTb hI => (hsmall b hbc hTb hI).le)
  exact closed_backward_mildPath_gives_strict_trajectory_extension
    hDensity hSob h0 hfree hret hefree heret hH hTc.le u0 U hc hT w hm

/-- An actual original-data extension contains the finite left endpoint. -/
theorem exists_extension_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hTa : T < a) (hU : Set.Ioc T a ⊆ U.domain)
    (hbound : ∀ t ∈ Set.Ioc T a, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSAfter U T) :
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊆ V.domain ∧ T ∈ V.domain ∧ Set.EqOn V.state U.state U.domain := by
  by_cases hT : T ∈ U.domain
  · exact ⟨U, Set.Subset.rfl, hT, fun _ _ => rfl⟩
  · obtain ⟨V, hUV, hTV, he⟩ := exists_strict_extension_of_finite_s
      hDensity hSob h0 hfree hret hefree heret hH u0 U hTa hU hT hbound hfiniteS
    exact ⟨V, hUV.subset, hTV, he⟩

/-- The extension supplies a closed literal backward mild path with the
original terminal datum and full accepted endpoint coordinates. -/
theorem exists_closed_backward_mild_fullZ_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hTa : T < a) (hU : Set.Ioc T a ⊆ U.domain)
    (hbound : ∀ t ∈ Set.Ioc T a, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSAfter U T) :
    ∃ w : CriticalPath (intervalMeasure T a),
      (∀ t : Set.Icc T a, T < (t : ℝ) → energyPath _ w t = U.state t) ∧
      IsBackwardMildHartreePath hTa.le alpha kernel u0 w ∧ FullZPath w := by
  obtain ⟨V, _, hTV, hEq⟩ := exists_extension_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH u0 U hTa hU hbound hfiniteS
  have hI : Set.Icc T a ⊆ V.domain := V.domain_connected.out' hTV V.center_mem
  let w := V.path hTa.le hI
  have hf := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    hTa.le (V.state T) w).mp (V.path_mild hTa.le hI)
  have hb := forwardFixedPoint_is_backward_at_terminal hDensity hSob h0 hfree hret hH
    hTa.le (V.state T) w hf
  have he : energyPath _ w ⟨a, hTa.le, le_rfl⟩ = u0 :=
    (V.path_agrees hTa.le hI ⟨a, hTa.le, le_rfl⟩).trans V.initial
  rw [he] at hb
  refine ⟨w, ?_, (isBackwardMildHartreePath_iff_fixedPoint
    hDensity hSob h0 hfree hret hH hTa.le u0 w).mpr hb, ?_⟩
  · intro t ht
    exact (V.path_agrees hTa.le hI t).trans (hEq (hU ⟨ht, t.property.2⟩))
  · exact V.path_fullZ hDensity hSob h0 hfree hret hefree heret hH hTa.le hI

/-- Membership refers to the original marked datum and its actual maximal domain. -/
theorem finite_s_left_endpoint_mem_maximalDomain (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hTa : T < a) (hU : Set.Ioc T a ⊆ U.domain)
    (hbound : ∀ t ∈ Set.Ioc T a, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSAfter U T) : T ∈ maximalDomain alpha kernel a u0 := by
  obtain ⟨V, _, hTV, _⟩ := exists_extension_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH u0 U hTa hU hbound hfiniteS
  exact subset_maximalDomain V hTV

/-- At an excluded finite left endpoint of an actual maximal trajectory,
a state cap excludes finite genuine S. -/
theorem maximal_finite_left_endpoint_not_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hmax : U.domain = maximalDomain alpha kernel a u0)
    (hTa : T < a) (hU : Set.Ioc T a ⊆ U.domain) (hT : T ∉ U.domain)
    (hbound : ∀ t ∈ Set.Ioc T a, ‖U.state t‖ ≤ B) : ¬ FiniteSAfter U T := by
  intro hfiniteS
  apply hT
  rw [hmax]
  exact finite_s_left_endpoint_mem_maximalDomain hDensity hSob h0 hfree hret
    hefree heret hH u0 U hTa hU hbound hfiniteS

/-- The paper's pure homogeneous H1 cap gives the actual state cap solely by
Sobolev norm comparison, with no L2, variance or energy conservation input. -/
theorem pure_gradient_actual_state_cap {K alpha kernel a T B : ℝ}
    (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0)
    (hgradient : ∀ t ∈ Set.Ioc T a, pureGradientNorm (U.state t) ≤ B) :
    ∀ t ∈ Set.Ioc T a, ‖U.state t‖ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * B := by
  intro t ht
  have hC : 0 ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 := le_trans zero_le_one (le_max_right _ _)
  exact (energyState_le_pureGradient hSob (U.state t)).trans
    (mul_le_mul_of_nonneg_left (hgradient t ht) hC)

#print axioms exists_threshold_uniform_critical_norm_on_left_tail
#print axioms exists_strict_extension_of_finite_s
#print axioms exists_extension_of_finite_s
#print axioms exists_closed_backward_mild_fullZ_of_finite_s
#print axioms finite_s_left_endpoint_mem_maximalDomain
#print axioms maximal_finite_left_endpoint_not_finite_s
#print axioms pure_gradient_actual_state_cap
end HartreeF.LeftFiniteSContinuation
