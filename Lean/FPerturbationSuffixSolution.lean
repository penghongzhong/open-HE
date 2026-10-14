import FPartitionSuffixGeometry
import FActualSingletonBackwardSolution
import FPerturbationPrefixSolution

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.BackwardFinitePerturbation
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalPathGluing
open ActualDuhamelPath ActualPathPartitions TimePartition ActualPerturbation FinitePerturbation
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness EndpointOutput
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  restrictPath gluePath hartreeDuhamelMap backwardHartreeDuhamelMap criticalPathIntervalSource
  referenceAt suffixPiecePath piecePath

/-- A genuinely constructed suffix retains the original prescribed terminal datum. -/
structure SuffixSolution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (D epsilon H : ℝ) (k : Fin (P.count+1)) where
  curve : CriticalPath (intervalMeasure (P.time k) (P.time (Fin.last P.count)))
  fixed : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH
    (P.ordered (Fin.le_last k)) f curve=curve
  fullZ : FullZPath curve
  initial_close : ‖energyPath _ curve ⟨P.time k,le_rfl,P.ordered (Fin.le_last k)⟩-
    referenceAt P q k‖ ≤ D^(P.count-k.val)*epsilon
  pieces : ∀ (i : Fin P.count) (hi : k.val ≤ i.val),
    ‖suffixPiecePath P k curve i hi-piecePath P q i‖ ≤ D^P.count*epsilon ∧
    FullZPath (suffixPiecePath P k curve i hi-piecePath P q i) ∧
    fullZSDifferenceSize (suffixPiecePath P k curve i hi) (piecePath P q i) ≤ ENNReal.ofReal H

/-- The reverse induction starts from a real singleton solution with true energy error. -/
def lastSuffixSolution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che alpha c a b D epsilon H : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (hH : OrdinaryHLS alpha c) (P : Partition a b) (f : EnergyState)
    (q : CriticalPath (intervalMeasure a b))
    (hf : ‖f-referenceAt P q (Fin.last P.count)‖ ≤ epsilon) :
    SuffixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H (Fin.last P.count) where
  curve := singletonBackwardPath hDensity hSob hfree (P.time (Fin.last P.count)) f
  fixed := singletonBackwardPath_fixed hDensity hSob h0 hfree hret hH (P.time (Fin.last P.count)) f
  fullZ := singletonBackwardPath_fullZ hDensity hSob hfree hefree (P.time (Fin.last P.count)) f
  initial_close := by
    have he := singletonBackwardPath_terminal hDensity hSob hfree (P.time (Fin.last P.count)) f
    have hb := (congrArg (fun z : EnergyState => ‖z-referenceAt P q (Fin.last P.count)‖) he).trans_le hf
    exact hb.trans_eq (by rw [Fin.val_last,Nat.sub_self,pow_zero,one_mul])
  pieces i hi := by
    have hf : False := by change P.count ≤ i.val at hi; omega
    exact hf.elim

/-- Add one actual backward local solution on the left of a constructed suffix.
Directional rebasing is used only to invoke the existing real concatenation theorem. -/
def prependSuffixSolution (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b D epsilon H : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (P : Partition a b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (i : Fin P.count)
    (s : SuffixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H i.succ)
    (v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)))
    (hfix : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH (piece_order P i)
      (energyPath _ s.curve ⟨P.time i.succ,le_rfl,P.ordered (Fin.le_last i.succ)⟩) v=v)
    (hz : FullZPath v)
    (hc : ‖v-piecePath P q i‖ ≤ D^(P.count-i.val)*epsilon)
    (hg : ‖v-piecePath P q i‖ ≤ D^P.count*epsilon)
    (hdz : FullZPath (v-piecePath P q i))
    (hs : fullZSDifferenceSize v (piecePath P q i) ≤ ENNReal.ofReal H) :
    SuffixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H i.castSucc := by
  let hac := piece_order P i
  let hcb := P.ordered (Fin.le_last i.succ)
  let g := energyPath _ s.curve ⟨P.time i.succ,le_rfl,hcb⟩
  let u0 := energyPath _ v ⟨P.time i.castSucc,le_rfl,hac⟩
  have hm : energyPath _ v ⟨P.time i.succ,hac,le_rfl⟩ =
      energyPath _ s.curve ⟨P.time i.succ,le_rfl,hcb⟩ :=
    actual_backward_fixedPoint_terminal hDensity hSob h0 hfree hret hH hac g v hfix
  let w := gluePath hac hcb v s.curve hm
  have hvf := backwardFixedPoint_is_forward_at_initial hDensity hSob h0 hfree hret hH hac g v hfix
  have hsf := backwardFixedPoint_is_forward_at_initial hDensity hSob h0 hfree hret hH hcb f s.curve s.fixed
  have hsf' : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb
      (energyPath _ v ⟨P.time i.succ,hac,le_rfl⟩) s.curve=s.curve :=
    (congrArg (fun z : EnergyState => hartreeDuhamelMap hDensity hSob h0 hfree hret hH hcb z s.curve) hm).trans hsf
  have hwf : hartreeDuhamelMap hDensity hSob h0 hfree hret hH (hac.trans hcb) u0 w=w :=
    gluePath_hartree_fixedPoint hDensity hSob h0 hfree hret hH hac hcb u0 v s.curve hm hvf hsf'
  have hwt : energyPath _ w ⟨P.time (Fin.last P.count),hac.trans hcb,le_rfl⟩=f :=
    (gluePath_energy hac hcb v s.curve hm ⟨P.time (Fin.last P.count),hac.trans hcb,le_rfl⟩).trans
      ((gluedEnergyPath_right hac hcb v s.curve hm ⟨P.time (Fin.last P.count),hcb,le_rfl⟩).trans
        (actual_backward_fixedPoint_terminal hDensity hSob h0 hfree hret hH hcb f s.curve s.fixed))
  have hwb := forwardFixedPoint_is_backward_at_terminal hDensity hSob h0 hfree hret hH
    (hac.trans hcb) u0 w hwf
  have hback : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH (hac.trans hcb) f w=w :=
    (congrArg (fun z : EnergyState => backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH
      (hac.trans hcb) z w) hwt).symm.trans hwb
  have hwl : energyPath _ w ⟨P.time i.castSucc,le_rfl,hac.trans hcb⟩=
      energyPath _ v ⟨P.time i.castSucc,le_rfl,hac⟩ :=
    (gluePath_energy hac hcb v s.curve hm ⟨P.time i.castSucc,le_rfl,hac.trans hcb⟩).trans
      (gluedEnergyPath_left hac hcb v s.curve hm ⟨P.time i.castSucc,le_rfl,hac⟩)
  refine ⟨w,hback,gluePath_fullZ hac hcb v s.curve hm hz s.fullZ,?_,?_⟩
  · exact (congrArg (fun z : EnergyState => ‖z-referenceAt P q i.castSucc‖) hwl).trans_le
      ((piece_initial_error_le P q i v).trans hc)
  · intro j hj
    by_cases heq : j=i
    · subst j
      have he : suffixPiecePath P i.castSucc w i hj=v := suffixPiecePath_glue_new P i v s.curve hm
      exact transport_piece_estimates _ v _ he ⟨hg,hdz,hs⟩
    · have hold : i.val+1 ≤ j.val := by
        change i.val ≤ j.val at hj
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h.symm)
        omega
      have he : suffixPiecePath P i.castSucc w j hj=suffixPiecePath P i.succ s.curve j hold :=
        suffixPiecePath_glue_old P i v s.curve hm j hold
      exact transport_piece_estimates _ _ _ he (s.pieces j hold)

end HartreeF.BackwardFinitePerturbation
