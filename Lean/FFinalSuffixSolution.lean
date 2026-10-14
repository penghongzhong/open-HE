import FPerturbationSuffixSolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.BackwardFinitePerturbation
open EnergySpace CriticalPathSpace CriticalPathRestriction ActualDuhamelPath
open ActualPathPartitions TimePartition ActualPerturbation FinitePerturbation
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain EndpointOutput
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  restrictPath backwardHartreeDuhamelMap criticalPathIntervalSource

/-- Equal-endpoint transport retains the original terminal datum and actual original pieces. -/
theorem transfer_suffix_endpoints (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b a0 b0 G H : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (hab0 : a0 ≤ b0) (hleft : a0=a) (hright : b0=b)
    (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (hl : ∀ i : Fin P.count, a0 ≤ P.time i.castSucc)
    (hr : ∀ i : Fin P.count, P.time i.succ ≤ b0)
    (hex : ∃ u : CriticalPath (intervalMeasure a0 b0),
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab0 f u=u ∧ FullZPath u ∧
      ∀ i : Fin P.count,
        ‖restrictPath (hl i) (piece_order P i) (hr i) u-piecePath P q i‖ ≤ G ∧
        FullZPath (restrictPath (hl i) (piece_order P i) (hr i) u-piecePath P q i) ∧
        fullZSDifferenceSize (restrictPath (hl i) (piece_order P i) (hr i) u) (piecePath P q i) ≤ ENNReal.ofReal H) :
    ∃ u : CriticalPath (intervalMeasure a b),
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u=u ∧ FullZPath u ∧
      ∀ i : Fin P.count,
        ‖piecePath P u i-piecePath P q i‖ ≤ G ∧ FullZPath (piecePath P u i-piecePath P q i) ∧
        fullZSDifferenceSize (piecePath P u i) (piecePath P q i) ≤ ENNReal.ofReal H := by
  subst a0
  subst b0
  simpa only [piecePath] using hex

/-- The zero-index suffix is the actual solution on the original entire interval. -/
theorem finalSuffix_solution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b D epsilon H : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (s : SuffixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H 0) :
    ∃ u : CriticalPath (intervalMeasure a b),
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u=u ∧ FullZPath u ∧
      ∀ i : Fin P.count,
        ‖piecePath P u i-piecePath P q i‖ ≤ D^P.count*epsilon ∧
        FullZPath (piecePath P u i-piecePath P q i) ∧
        fullZSDifferenceSize (piecePath P u i) (piecePath P q i) ≤ ENNReal.ofReal H := by
  have hs : ∃ u : CriticalPath (intervalMeasure (P.time 0) (P.time (Fin.last P.count))),
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH (P.ordered (Fin.zero_le _)) f u=u ∧ FullZPath u ∧
      ∀ i : Fin P.count,
        ‖suffixPiecePath P 0 u i (Nat.zero_le _)-piecePath P q i‖ ≤ D^P.count*epsilon ∧
        FullZPath (suffixPiecePath P 0 u i (Nat.zero_le _)-piecePath P q i) ∧
        fullZSDifferenceSize (suffixPiecePath P 0 u i (Nat.zero_le _)) (piecePath P q i) ≤ ENNReal.ofReal H :=
    ⟨s.curve,s.fixed,s.fullZ,fun i => s.pieces i (Nat.zero_le _)⟩
  exact transfer_suffix_endpoints hDensity hSob h0 hfree hret hH hab
    (P.ordered (Fin.zero_le _)) P.left P.right P f q
    (fun i => P.ordered (Fin.zero_le i.castSucc)) (fun i => P.ordered (Fin.le_last i.succ)) hs

end HartreeF.BackwardFinitePerturbation
