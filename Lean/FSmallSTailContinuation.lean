import FSmallSGraphBound
import FActualFiniteEndpointContinuation

/-! Internal continuation consumer for a small actual S tail. The finite-S
producer is deliberately separate; none of the results in this module alone
assert the finite-S criterion. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.MaximalTrajectory.LocalMildTrajectory
open EnergySpace CriticalPathSpace
variable {alpha kernel a : ℝ} {u0 : EnergyState}

/-- Change the marked datum without changing the actual domain, state or
compact mild paths. -/
def recenterWithDatum (U : LocalMildTrajectory alpha kernel a u0)
    (c : ℝ) (v0 : EnergyState) (hc : c ∈ U.domain) (hinit : U.state c = v0) :
    LocalMildTrajectory alpha kernel c v0 where
  domain := U.domain
  state := U.state
  domain_open := U.domain_open
  domain_connected := U.domain_connected
  center_mem := hc
  continuous := U.continuous
  initial := hinit
  compact := U.compact

def recenter (U : LocalMildTrajectory alpha kernel a u0)
    (c : ℝ) (hc : c ∈ U.domain) :
    LocalMildTrajectory alpha kernel c (U.state c) :=
  U.recenterWithDatum c (U.state c) hc rfl

theorem recenter_path (U : LocalMildTrajectory alpha kernel a u0)
    (c : ℝ) (hc : c ∈ U.domain) {l r : ℝ} (hlr : l ≤ r)
    (hI : Set.Icc l r ⊆ U.domain) :
    (U.recenter c hc).path hlr hI = U.path hlr hI := rfl

end HartreeF.MaximalTrajectory.LocalMildTrajectory

namespace HartreeF.FiniteSContinuation
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open Retarded ForcingDomain CriticalUniqueness MaximalTrajectory EndpointOutput
open SobolevStretch StationarySelfTest ActualStrichartz CriticalSourceBounds
open SmallSGraphBound FiniteEndpoint
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution criticalPathIntervalSource hartreeDuhamelMap

/-- A pointwise bound on the actual trajectory gives the compact continuous
energy-coordinate norm bound, including zero-width intervals. -/
theorem compact_energy_coordinate_bound {alpha kernel a T B : ℝ}
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hB : 0 ≤ B) (hbound : ∀ t ∈ Set.Ico a T, ‖U.state t‖ ≤ B)
    {c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (hbT : b < T)
    (hI : Set.Icc c b ⊆ U.domain) :
    ‖energyPath (intervalMeasure c b) (U.path hcb hI)‖ ≤ B := by
  apply (ContinuousMap.norm_le _ hB).mpr
  intro t
  rw [U.path_agrees]
  exact hbound t ⟨hac.trans t.property.1, t.property.2.trans_lt hbT⟩

/-- The small-S threshold is selected before the tail center. A small actual
S bound on every tail prefix then produces a uniform actual E+W graph bound
for the recentered trajectory. This is an internal consumer, not a finite-S
assumption or a replacement for the tail producer. -/
theorem exists_threshold_uniform_critical_norm_on_tail (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hB : 0 ≤ B) (hbound : ∀ t ∈ Set.Ico a T, ‖U.state t‖ ≤ B) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ (c : ℝ) (_hac : a ≤ c)
      (hc : c ∈ U.domain),
      (∀ (b : ℝ) (hcb : c ≤ b), b < T → ∀ hI : Set.Icc c b ⊆ U.domain,
        pathValueSize (intervalMeasure c b) (U.path hcb hI) ≤ ENNReal.ofReal eta) →
      UniformCriticalNormBefore (U.recenter c hc) T
        (2 * max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖U.state c‖) := by
  obtain ⟨eta, heta, heta1, hgraph⟩ :=
    exists_small_s_energy_coordinate_graph_bound hDensity hSob h0 hfree hret hH hB
  refine ⟨eta, heta, heta1, ?_⟩
  intro c hac hc hsmall b hcb hbT hI
  change ‖U.path hcb hI‖ ≤ _
  exact hgraph hcb (U.state c) (U.path hcb hI) (U.path_mild hcb hI)
    (compact_energy_coordinate_bound U hB hbound hac hcb hbT hI)
    (hsmall b hcb hbT hI)

/-- Transport an actual strict extension at a tail center back to the original
datum. The equality on the old domain supplies the original initial value. -/
theorem strict_extension_from_recenter {alpha kernel a c T : ℝ}
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hc : c ∈ U.domain)
    (V : LocalMildTrajectory alpha kernel c (U.state c))
    (hUV : (U.recenter c hc).domain ⊂ V.domain)
    (hTV : T ∈ V.domain)
    (hEq : Set.EqOn V.state (U.recenter c hc).state (U.recenter c hc).domain) :
    ∃ W : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊂ W.domain ∧ T ∈ W.domain ∧ Set.EqOn W.state U.state U.domain := by
  have haV : a ∈ V.domain := hUV.subset U.center_mem
  have hinit : V.state a = u0 := (hEq U.center_mem).trans U.initial
  exact ⟨V.recenterWithDatum a u0 haV hinit, hUV, hTV, hEq⟩

/-- Internal criterion: actual energy control and an eventual small actual-S
tail produce a strict extension of the original trajectory. -/
theorem exists_strict_extension_of_small_s_tails (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a T B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Ico a T ⊆ U.domain) (hT : T ∉ U.domain)
    (hB : 0 ≤ B) (hbound : ∀ t ∈ Set.Ico a T, ‖U.state t‖ ≤ B)
    (htails : ∀ eta : ℝ, 0 < eta → ∃ c ∈ Set.Ioo a T,
      ∀ (b : ℝ) (hcb : c ≤ b), b < T → ∀ hI : Set.Icc c b ⊆ U.domain,
        pathValueSize (intervalMeasure c b) (U.path hcb hI) ≤ ENNReal.ofReal eta) :
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊂ V.domain ∧ T ∈ V.domain ∧ Set.EqOn V.state U.state U.domain := by
  obtain ⟨eta, heta, _, hgraph⟩ := exists_threshold_uniform_critical_norm_on_tail
    hDensity hSob h0 hfree hret hH u0 U hB hbound
  obtain ⟨c, hc, hsmall⟩ := htails eta heta
  have hcU : c ∈ U.domain := hU ⟨hc.1.le, hc.2⟩
  have htail : Set.Ico c T ⊆ (U.recenter c hcU).domain := by
    intro t ht
    exact hU ⟨hc.1.le.trans ht.1, ht.2⟩
  obtain ⟨V, hUV, hTV, hEq⟩ := exists_strict_extension_of_uniform_critical_norm
    hDensity hSob h0 hfree hret hefree heret hH (U.state c) (U.recenter c hcU)
    hc.2 htail hT (hgraph c hc.1.le hcU hsmall)
  exact strict_extension_from_recenter U hcU V hUV hTV hEq

#print axioms HartreeF.FiniteSContinuation.compact_energy_coordinate_bound
#print axioms HartreeF.FiniteSContinuation.exists_threshold_uniform_critical_norm_on_tail
#print axioms HartreeF.FiniteSContinuation.strict_extension_from_recenter
#print axioms HartreeF.FiniteSContinuation.exists_strict_extension_of_small_s_tails
end HartreeF.FiniteSContinuation
