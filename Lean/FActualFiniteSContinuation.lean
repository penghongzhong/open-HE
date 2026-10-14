import FSmallSTailContinuation
import FActualFiniteSTail

/-! Actual finite-S continuation at a finite right endpoint. The genuine
compact-prefix S bound is consumed by the global L10 realization/tail producer;
the small-S consumer then constructs an actual extension at the original datum.
No W bound, energy conservation law, tail estimate, or limiting state is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteSContinuation
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded ForcingDomain CriticalUniqueness MaximalTrajectory EndpointOutput
open SobolevStretch StationarySelfTest ActualStrichartz CriticalSourceBounds ActualSTail
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution criticalPathIntervalSource hartreeDuhamelMap

/-- The finite-S hypothesis is literal uniform finiteness of the actual compact
prefix L10_t L10_x quantities. It contains no W or tail hypothesis. -/
def FiniteSBefore {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) (T : ℝ) : Prop :=
  ∃ M : ℝ≥0, UniformSNormBefore U a T M

/-- An actual trajectory with bounded energy coordinate and finite actual S
has an actual strict extension across its excluded finite right endpoint. -/
theorem exists_strict_extension_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain) (hT : T ∉ U.domain)
    (hbound : ∀ t ∈ Set.Ico a T, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSBefore U T) :
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊂ V.domain ∧ T ∈ V.domain ∧ Set.EqOn V.state U.state U.domain := by
  obtain ⟨M, hS⟩ := hfiniteS
  have hB : 0 ≤ B := (norm_nonneg (U.state a)).trans (hbound a ⟨le_rfl, haT⟩)
  apply exists_strict_extension_of_small_s_tails hDensity hSob h0 hfree hret
    hefree heret hH u0 U hU hT hB hbound
  intro eta heta
  obtain ⟨c, hac, hcT, hsmall⟩ :=
    exists_uniform_small_s_tail hDensity hSob U haT hU M hS heta
  exact ⟨c, ⟨hac, hcT⟩, fun b hcb hbT hI => (hsmall b hcb hbT hI).le⟩

/-- The finite-S criterion yields an actual extension containing the endpoint,
also covering trajectories whose domain already contains it. -/
theorem exists_extension_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain)
    (hbound : ∀ t ∈ Set.Ico a T, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSBefore U T) :
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊆ V.domain ∧ T ∈ V.domain ∧ Set.EqOn V.state U.state U.domain := by
  by_cases hT : T ∈ U.domain
  · exact ⟨U, Set.Subset.rfl, hT, fun _ _ => rfl⟩
  · obtain ⟨V, hUV, hTV, hEq⟩ := exists_strict_extension_of_finite_s
      hDensity hSob h0 hfree hret hefree heret hH u0 U haT hU hT hbound hfiniteS
    exact ⟨V, hUV.subset, hTV, hEq⟩

/-- Actual finite-S continuation supplies a closed original-data mild path and
all accepted endpoint Z coordinates, with agreement on the original interval. -/
theorem exists_closed_mild_fullZ_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain)
    (hbound : ∀ t ∈ Set.Ico a T, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSBefore U T) :
    ∃ w : CriticalPath (intervalMeasure a T),
      (∀ t : Set.Icc a T, (t : ℝ) < T → energyPath _ w t = U.state t) ∧
      IsMildHartreePath haT.le alpha kernel u0 w ∧ FullZPath w := by
  obtain ⟨V, _, hTV, hEq⟩ := exists_extension_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH u0 U haT hU hbound hfiniteS
  have hI : Set.Icc a T ⊆ V.domain := V.domain_connected.out' V.center_mem hTV
  refine ⟨V.path haT.le hI, ?_, ?_, ?_⟩
  · intro t ht
    exact (V.path_agrees haT.le hI t).trans (hEq (hU ⟨t.property.1, ht⟩))
  · simpa only [V.initial] using V.path_mild haT.le hI
  · exact V.path_fullZ hDensity hSob h0 hfree hret hefree heret hH haT.le hI

/-- Endpoint membership is for the original datum and the actual maximal
domain, not just the recentered auxiliary trajectory. -/
theorem finite_s_endpoint_mem_maximalDomain (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain)
    (hbound : ∀ t ∈ Set.Ico a T, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSBefore U T) :
    T ∈ maximalDomain alpha kernel a u0 := by
  obtain ⟨V, _, hTV, _⟩ := exists_extension_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH u0 U haT hU hbound hfiniteS
  exact subset_maximalDomain V hTV

/-- At an excluded finite right endpoint of an actual maximal trajectory with
a bounded actual energy coordinate, finite actual S is impossible. -/
theorem maximal_finite_right_endpoint_not_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hmax : U.domain = maximalDomain alpha kernel a u0)
    (haT : a < T) (hU : Set.Ico a T ⊆ U.domain) (hT : T ∉ U.domain)
    (hbound : ∀ t ∈ Set.Ico a T, ‖U.state t‖ ≤ B) :
    ¬ FiniteSBefore U T := by
  intro hfiniteS
  apply hT
  rw [hmax]
  exact finite_s_endpoint_mem_maximalDomain hDensity hSob h0 hfree hret
    hefree heret hH u0 U haT hU hbound hfiniteS

#print axioms HartreeF.FiniteSContinuation.exists_strict_extension_of_finite_s
#print axioms HartreeF.FiniteSContinuation.exists_extension_of_finite_s
#print axioms HartreeF.FiniteSContinuation.exists_closed_mild_fullZ_of_finite_s
#print axioms HartreeF.FiniteSContinuation.finite_s_endpoint_mem_maximalDomain
#print axioms HartreeF.FiniteSContinuation.maximal_finite_right_endpoint_not_finite_s
end HartreeF.FiniteSContinuation
