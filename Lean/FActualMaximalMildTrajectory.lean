import FLocalMildTrajectoryExistence
import FMaximalMildTrajectoryUnion

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.MaximalTrajectory
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathRestriction CriticalUniqueness SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath energyDistribution hartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- The actual maximal open-interval Hartree trajectory, constructed from the
union of all actual local mild trajectories. The centered producer, overlap
uniqueness, continuity, and compact-interval gluing are all instantiated here. -/
def actualMaximalTrajectory (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (s0 : ℝ) (u0 : EnergyState) :
    LocalMildTrajectory alpha kernel s0 u0 := by
  let U := Classical.choice (exists_localMildTrajectory
    hDensity hSob h0 hfree hret hefree heret hH s0 u0)
  exact {
    domain := maximalDomain alpha kernel s0 u0
    state := maximalState alpha kernel s0 u0
    domain_open := maximalDomain_open
    domain_connected := maximalDomain_connected
    center_mem := subset_maximalDomain U U.center_mem
    continuous := maximalState_continuous hDensity hSob h0 hfree hret hH
    initial := (maximalState_agrees hDensity hSob h0 hfree hret hH U U.center_mem).trans U.initial
    compact := fun hab hI => maximalState_compact hDensity hSob h0 hfree hret hH hab hI }

/-- Maximal lifespan existence and uniqueness in the actual local critical
mild class, with full Z regularity on every compact interval. All internal
Hartree producers are discharged. Only the existing ordinary eight analytic
premises remain; conservation, continuation criteria and scattering are not
asserted here. -/
theorem exists_actual_maximal_mild_fullZ (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (s0 : ℝ) (u0 : EnergyState) :
    ∃ M : LocalMildTrajectory alpha kernel s0 u0,
      M.domain = maximalDomain alpha kernel s0 u0 ∧
      (∀ V : LocalMildTrajectory alpha kernel s0 u0,
        V.domain ⊆ M.domain ∧ Set.EqOn M.state V.state V.domain) ∧
      (∀ {a b : ℝ} (hab : a ≤ b), Set.Icc a b ⊆ M.domain →
        ∃ u : CriticalPath (intervalMeasure a b),
          (∀ t : Set.Icc a b, energyPath _ u t = M.state t) ∧
          IsMildHartreePath hab alpha kernel (M.state a) u ∧ FullZPath u) ∧
      (∀ V : LocalMildTrajectory alpha kernel s0 u0, M.domain ⊆ V.domain →
        V.domain = M.domain ∧ Set.EqOn V.state M.state M.domain) := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
  have hdom : M.domain = maximalDomain alpha kernel s0 u0 := rfl
  have hmax : ∀ V : LocalMildTrajectory alpha kernel s0 u0,
      V.domain ⊆ M.domain ∧ Set.EqOn M.state V.state V.domain := by
    intro V
    refine ⟨?_, ?_⟩
    · exact subset_maximalDomain V
    · intro t ht
      exact maximalState_agrees hDensity hSob h0 hfree hret hH V ht
  refine ⟨M, hdom, hmax, ?_, ?_⟩
  · intro a b hab hI
    exact ⟨M.path hab hI, M.path_agrees hab hI, M.path_mild hab hI,
      LocalMildTrajectory.path_fullZ hDensity hSob h0 hfree hret hefree heret hH M hab hI⟩
  · intro V hMV
    have he : V.domain = M.domain := Set.Subset.antisymm (hmax V).1 hMV
    refine ⟨he, ?_⟩
    intro t ht
    exact ((hmax V).2 (hMV ht)).symm

end HartreeF.MaximalTrajectory
