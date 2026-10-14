import FPerturbationPrefixSolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.FinitePerturbation
open EnergySpace CriticalPathSpace CriticalPathRestriction ActualDuhamelPath
open ActualPathPartitions TimePartition ActualPerturbation SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  restrictPath hartreeDuhamelMap criticalPathIntervalSource

/-- Reindex only equal closed endpoints; the original partition and q remain fixed. -/
theorem transfer_prefix_endpoints (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b a0 b0 D epsilon H : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (hab0 : a0 ≤ b0) (hleft : a0=a) (hright : b0=b)
    (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (hl : ∀ i : Fin P.count, a0 ≤ P.time i.castSucc)
    (hr : ∀ i : Fin P.count, P.time i.succ ≤ b0)
    (hex : ∃ u : CriticalPath (intervalMeasure a0 b0),
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab0 f u=u ∧ FullZPath u ∧
      ∀ i : Fin P.count,
        ‖restrictPath (hl i) (piece_order P i) (hr i) u-piecePath P q i‖ ≤ D^(i.val+1)*epsilon ∧
        FullZPath (restrictPath (hl i) (piece_order P i) (hr i) u-piecePath P q i) ∧
        fullZSDifferenceSize (restrictPath (hl i) (piece_order P i) (hr i) u) (piecePath P q i) ≤ ENNReal.ofReal H) :
    ∃ u : CriticalPath (intervalMeasure a b),
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u=u ∧ FullZPath u ∧
      ∀ i : Fin P.count,
        ‖piecePath P u i-piecePath P q i‖ ≤ D^(i.val+1)*epsilon ∧
        FullZPath (piecePath P u i-piecePath P q i) ∧
        fullZSDifferenceSize (piecePath P u i) (piecePath P q i) ≤ ENNReal.ofReal H := by
  subst a0
  subst b0
  simpa only [piecePath] using hex

/-- The last true prefix is an actual solution on the original closed interval. -/
theorem finalPrefix_solution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b D epsilon H : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (s : PrefixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H P.count le_rfl) :
    ∃ u : CriticalPath (intervalMeasure a b),
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u=u ∧ FullZPath u ∧
      ∀ i : Fin P.count,
        ‖piecePath P u i-piecePath P q i‖ ≤ D^(i.val+1)*epsilon ∧
        FullZPath (piecePath P u i-piecePath P q i) ∧
        fullZSDifferenceSize (piecePath P u i) (piecePath P q i) ≤ ENNReal.ofReal H := by
  have hs : ∃ u : CriticalPath (intervalMeasure (P.time 0) (node P P.count le_rfl)),
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH (P.ordered (Fin.zero_le _)) f u=u ∧ FullZPath u ∧
      ∀ i : Fin P.count,
        ‖prefixPiecePath P P.count le_rfl u i i.isLt-piecePath P q i‖ ≤ D^(i.val+1)*epsilon ∧
        FullZPath (prefixPiecePath P P.count le_rfl u i i.isLt-piecePath P q i) ∧
        fullZSDifferenceSize (prefixPiecePath P P.count le_rfl u i i.isLt) (piecePath P q i) ≤ ENNReal.ofReal H :=
    ⟨s.curve,s.fixed,s.fullZ,fun i => s.pieces i i.isLt⟩
  exact transfer_prefix_endpoints hDensity hSob h0 hfree hret hH hab
    (P.ordered (Fin.zero_le _)) P.left (node_last P) P f q
    (fun i => P.ordered (Fin.zero_le i.castSucc))
    (fun i => P.ordered (Fin.le_last i.succ)) hs

end HartreeF.FinitePerturbation
