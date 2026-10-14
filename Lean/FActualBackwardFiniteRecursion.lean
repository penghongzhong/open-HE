import FPerturbationSuffixSolution
import FActualFinitePerturbationRecursion

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
open CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
open BackwardPerturbation BackwardPDEConsumer
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  restrictPath gluePath backwardHartreeDuhamelMap criticalPathIntervalSource
  CompatibleL1IntervalSource.advancedCriticalPath referenceAt

/-- The original PDE supplies each original piece's actual advanced forced identity. -/
theorem piece_backward_forced_identity (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
    (hgen : OrdinaryFreeDistributionScalarGenerator) (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hPDE : ForcedHartreeCompactTestIdentity alpha c hab q E)
    (P : Partition a b) (i : Fin P.count) :
    piecePath P q i = backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH (piece_order P i)
      (referenceAt P q i.succ) (piecePath P q i) +
      Complex.I • (pieceError P E i).advancedCriticalPath hDensity hSob h0 hfree hret := by
  have hpde : ForcedHartreeCompactTestIdentity alpha c (piece_order P i) (piecePath P q i) (pieceError P E i) :=
    ForcedHartreeCompactTestIdentity.restrict hab q E hPDE
      (P.mem_interval i.castSucc).1 (piece_order P i) (P.mem_interval i.succ).2
  have he := actual_backward_forced_graph_of_distributional hDensity hSob h0 hfree hret hH
    (piece_order P i) (piecePath P q i) (pieceError P E i) hgen hUnique hpde
  have ht : energyPath _ (piecePath P q i) ⟨P.time i.succ,piece_order P i,le_rfl⟩=referenceAt P q i.succ := by
    unfold referenceAt
    exact piecePath_energy P q i ⟨P.time i.succ,piece_order P i,le_rfl⟩
  exact he.trans (congrArg (fun z : EnergyState =>
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH (piece_order P i) z (piecePath P q i) +
      Complex.I • (pieceError P E i).advancedCriticalPath hDensity hSob h0 hfree hret) ht)

/-- Reverse induction on actual partition nodes produces every true terminal-data
suffix solution. It does not reflect time or assume solutions of the pieces. -/
theorem exists_actual_backward_perturbation_suffixes (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c)
    (hgen : OrdinaryFreeDistributionScalarGenerator) (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hB : 0 ≤ B) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f : EnergyState) (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
      (P : Partition a b) (epsilon : ℝ),
      ForcedHartreeCompactTestIdentity alpha c hab q E → ‖energyPath _ q‖ ≤ B →
      (∀ i : Fin P.count, ‖fun j => criticalGradient _ j (piecePath P q i)‖ ≤ r) →
      0 ≤ epsilon → ‖f-referenceAt P q (Fin.last P.count)‖ ≤ epsilon → ‖E.gradient‖ ≤ epsilon →
      (iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
        (max (energyEndpointConstant K C0) (Ch*C0+Cr)))^(P.count+1)*epsilon ≤ r/2 →
      ∀ k : Fin (P.count+1), Nonempty (SuffixSolution hDensity hSob h0 hfree hret hH P f q
        (iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
          (max (energyEndpointConstant K C0) (Ch*C0+Cr))) epsilon
        (2*C*(iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
          (max (energyEndpointConstant K C0) (Ch*C0+Cr)))^P.count*epsilon) k) := by
  let choice := exists_actual_backward_solution_fullZ_of_small_forcing
    hDensity hSob h0 hfree hret hefree heret hH hB
  let r : ℝ := Classical.choose choice
  let cc := Classical.choose_spec choice
  let C : ℝ := Classical.choose cc
  have hs := Classical.choose_spec cc
  have hC : 0 < C := hs.2.2.1
  refine ⟨r,C,hs.1,hs.2.1,hC,?_⟩
  intro a b hab f q E P epsilon hPDE hqE hqW heps hf hE hsmall
  let Cf := max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch
  let Q := max (energyEndpointConstant K C0) (Ch*C0+Cr)
  let D := iterationMultiplier Cf Q
  let H := 2*C*D^P.count*epsilon
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hD : 1 ≤ D := iterationMultiplier_one_le hCf hQ
  have hstep (i : Fin P.count) (g : EnergyState)
      (hg : ‖g-referenceAt P q i.succ‖ ≤ D^(P.count-(i.val+1))*epsilon) :
      ∃ v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)),
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH (piece_order P i) g v=v ∧ FullZPath v ∧
        ‖v-piecePath P q i‖ ≤ D^(P.count-i.val)*epsilon ∧
        ‖v-piecePath P q i‖ ≤ D^P.count*epsilon ∧
        FullZPath (v-piecePath P q i) ∧ fullZSDifferenceSize v (piecePath P q i) ≤ ENNReal.ofReal H := by
    let j := P.count-(i.val+1)
    have hj : j < P.count := by dsimp [j]; omega
    have hjnext : j+1=P.count-i.val := by dsimp [j]; omega
    have he := (pieceError_gradient_norm_le P E i).trans hE
    have hseed := iteration_seed_bounds hCf hQ heps hj hg he hsmall
    let result := hs.2.2.2 (piece_order P i) g (referenceAt P q i.succ)
      (piecePath P q i) (pieceError P E i)
      (piece_backward_forced_identity hDensity hSob h0 hfree hret hH hab q E hgen hUnique hPDE P i)
      ((piece_energy_norm_le P q i).trans hqE) (hqW i) hseed.1
    let v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)) := Classical.choose result
    have hv := Classical.choose_spec result
    have hclose : ‖v-piecePath P q i‖ ≤ D^(P.count-i.val)*epsilon :=
      hv.2.2.2.2.1.trans (hseed.2.trans_eq (congrArg (fun n : ℕ => D^n*epsilon) hjnext))
    have hglobal : ‖v-piecePath P q i‖ ≤ D^P.count*epsilon := hclose.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (Nat.sub_le _ _)) heps)
    have hsize := iteration_piece_size_bound hD heps hC.le (Nat.sub_le P.count (i.val+1)) hg he
    refine ⟨v,(isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      (piece_order P i) g v).mp hv.1,hv.2.1,hclose,hglobal,hv.2.2.1,?_⟩
    exact hv.2.2.2.2.2.1.trans (ENNReal.ofReal_le_ofReal hsize)
  apply Fin.reverseInduction
  · exact ⟨lastSuffixSolution hDensity hSob h0 hfree hret hefree hH P f q hf⟩
  · intro i hi
    let s : SuffixSolution hDensity hSob h0 hfree hret hH P f q D epsilon H i.succ := Classical.choice hi
    let g := energyPath _ s.curve ⟨P.time i.succ,le_rfl,P.ordered (Fin.le_last i.succ)⟩
    let result := hstep i g s.initial_close
    let v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)) := Classical.choose result
    have hv := Classical.choose_spec result
    exact ⟨prependSuffixSolution hDensity hSob h0 hfree hret hH P f q i s v
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2.1 hv.2.2.2.2.2⟩

end HartreeF.BackwardFinitePerturbation
