import FPartitionPrefixGeometry
import FActualFullZForcingPerturbation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.FinitePerturbation
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalPathGluing
open ActualDuhamelPath ActualPathPartitions TimePartition ActualPerturbation
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness EndpointOutput
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  restrictPath gluePath hartreeDuhamelMap criticalPathIntervalSource

def referenceState {a b : ℝ} (P : Partition a b) (q : CriticalPath (intervalMeasure a b))
    (n : ℕ) (hn : n ≤ P.count) : EnergyState :=
  energyPath _ q ⟨node P n hn,node_mem P n hn⟩

attribute [local irreducible] referenceState prefixPiecePath piecePath

theorem transport_piece_estimates {a b G H : ℝ}
    (u v q : CriticalPath (intervalMeasure a b)) (he : u=v)
    (hv : ‖v-q‖ ≤ G ∧ FullZPath (v-q) ∧ fullZSDifferenceSize v q ≤ ENNReal.ofReal H) :
    ‖u-q‖ ≤ G ∧ FullZPath (u-q) ∧ fullZSDifferenceSize u q ≤ ENNReal.ofReal H :=
  (congrArg (fun w : CriticalPath (intervalMeasure a b) =>
    ‖w-q‖ ≤ G ∧ FullZPath (w-q) ∧ fullZSDifferenceSize w q ≤ ENNReal.ofReal H) he).mpr hv

/-- A constructed actual prefix, including its exact old-piece restrictions. -/
structure PrefixSolution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (D epsilon H : ℝ) (n : ℕ) (hn : n ≤ P.count) where
  curve : CriticalPath (intervalMeasure (P.time 0) (node P n hn))
  fixed : hartreeDuhamelMap hDensity hSob h0 hfree hret hH
    (P.ordered (Fin.zero_le _)) f curve = curve
  fullZ : FullZPath curve
  terminal_close : ‖energyPath _ curve ⟨node P n hn,P.ordered (Fin.zero_le _),le_rfl⟩-
    referenceState P q n hn‖ ≤ D^n*epsilon
  pieces : ∀ (i : Fin P.count) (hi : i.val < n),
    ‖prefixPiecePath P n hn curve i hi-piecePath P q i‖ ≤ D^(i.val+1)*epsilon ∧
    FullZPath (prefixPiecePath P n hn curve i hi-piecePath P q i) ∧
    fullZSDifferenceSize (prefixPiecePath P n hn curve i hi) (piecePath P q i) ≤ ENNReal.ofReal H

/-- A graph error on the actual nth piece controls the next real endpoint error. -/
theorem piece_terminal_error_le {a b : ℝ} (P : Partition a b)
    (q : CriticalPath (intervalMeasure a b)) (i : Fin P.count)
    (v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ))) :
    ‖energyPath _ v ⟨P.time i.succ,piece_order P i,le_rfl⟩-
      referenceState P q (i.val+1) i.isLt‖ ≤ ‖v-piecePath P q i‖ := by
  have he := criticalPath_energy_sub_apply v (piecePath P q i)
    ⟨P.time i.succ,piece_order P i,le_rfl⟩
  have href : energyPath _ (piecePath P q i) ⟨P.time i.succ,piece_order P i,le_rfl⟩ =
      referenceState P q (i.val+1) i.isLt := by
    unfold piecePath
    rw [restrictPath_energy]
    unfold referenceState
    rfl
  have he' := he.trans (congrArg (fun z : EnergyState =>
    energyPath _ v ⟨P.time i.succ,piece_order P i,le_rfl⟩-z) href)
  exact (congrArg norm he').symm.le.trans
    (energyPath_value_norm_le _ (v-piecePath P q i) ⟨P.time i.succ,piece_order P i,le_rfl⟩)

/-- The first produced short solution is the first actual prefix. -/
def firstPrefixSolution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b D epsilon H : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (v : CriticalPath (intervalMeasure (P.time (⟨0,P.positive⟩ : Fin P.count).castSucc)
      (P.time (⟨0,P.positive⟩ : Fin P.count).succ)))
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH (piece_order P ⟨0,P.positive⟩) f v=v)
    (hz : FullZPath v)
    (hc : ‖v-piecePath P q ⟨0,P.positive⟩‖ ≤ D^1*epsilon)
    (hdz : FullZPath (v-piecePath P q ⟨0,P.positive⟩))
    (hs : fullZSDifferenceSize v (piecePath P q ⟨0,P.positive⟩) ≤ ENNReal.ofReal H) :
    PrefixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H 1 P.positive where
  curve := v
  fixed := hfix
  fullZ := hz
  terminal_close := (piece_terminal_error_le P q ⟨0,P.positive⟩ v).trans hc
  pieces i hi := by
    have hi0 : i=(⟨0,P.positive⟩ : Fin P.count) := Fin.ext (by change i.val = 0; omega)
    subst i
    have he := prefixPiecePath_first P v
    exact transport_piece_estimates _ v _ he ⟨hc,hdz,hs⟩

/-- Append a genuinely constructed local solution to the existing prefix. -/
def appendPrefixSolution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b D epsilon H : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    {n : ℕ} (hn : n < P.count)
    (s : PrefixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H n hn.le)
    (v : CriticalPath (intervalMeasure (P.time (⟨n,hn⟩ : Fin P.count).castSucc)
      (P.time (⟨n,hn⟩ : Fin P.count).succ)))
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH (piece_order P ⟨n,hn⟩)
      (energyPath _ s.curve ⟨node P n hn.le,P.ordered (Fin.zero_le _),le_rfl⟩) v=v)
    (hz : FullZPath v)
    (hc : ‖v-piecePath P q ⟨n,hn⟩‖ ≤ D^(n+1)*epsilon)
    (hdz : FullZPath (v-piecePath P q ⟨n,hn⟩))
    (hs : fullZSDifferenceSize v (piecePath P q ⟨n,hn⟩) ≤ ENNReal.ofReal H) :
    PrefixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H (n+1) hn := by
  let hac := P.ordered (Fin.zero_le (⟨n,Nat.lt_succ_of_le hn.le⟩ : Fin (P.count+1)))
  let hcb := piece_order P ⟨n,hn⟩
  have hm : energyPath _ s.curve ⟨node P n hn.le,hac,le_rfl⟩ =
      energyPath _ v ⟨node P n hn.le,le_rfl,hcb⟩ :=
    (actual_fixedPoint_initial hDensity hSob h0 hfree hret hH hcb
      (energyPath _ s.curve ⟨node P n hn.le,hac,le_rfl⟩) v hfix).symm
  let w := gluePath hac hcb s.curve v hm
  have hterminal : energyPath _ w ⟨node P (n+1) hn,hac.trans hcb,le_rfl⟩ =
      energyPath _ v ⟨node P (n+1) hn,hcb,le_rfl⟩ :=
    (gluePath_energy hac hcb s.curve v hm ⟨node P (n+1) hn,hac.trans hcb,le_rfl⟩).trans
      (gluedEnergyPath_right hac hcb s.curve v hm ⟨node P (n+1) hn,hcb,le_rfl⟩)
  refine ⟨w, gluePath_hartree_fixedPoint hDensity hSob h0 hfree hret hH hac hcb f
    s.curve v hm s.fixed hfix, gluePath_fullZ hac hcb s.curve v hm s.fullZ hz, ?_, ?_⟩
  · exact (congrArg (fun x : EnergyState => ‖x-referenceState P q (n+1) hn‖) hterminal).trans_le
      ((piece_terminal_error_le P q ⟨n,hn⟩ v).trans hc)
  · intro i hi
    by_cases hold : i.val < n
    · have he : prefixPiecePath P (n+1) hn w i hi = prefixPiecePath P n hn.le s.curve i hold :=
        prefixPiecePath_glue_old P hn s.curve v hm i hold
      exact transport_piece_estimates _ _ _ he (s.pieces i hold)
    · have hiN : i=(⟨n,hn⟩ : Fin P.count) := Fin.ext (by change i.val = n; omega)
      subst i
      have he : prefixPiecePath P (n+1) hn w ⟨n,hn⟩ hi = v :=
        prefixPiecePath_glue_new P hn s.curve v hm
      exact transport_piece_estimates _ v _ he ⟨hc,hdz,hs⟩

end HartreeF.FinitePerturbation
