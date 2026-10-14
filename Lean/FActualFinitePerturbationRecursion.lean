import FPerturbationPrefixSolution
import FPerturbationIterationArithmetic
import FActualHartreePDERestriction

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
open CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  restrictPath gluePath hartreeDuhamelMap criticalPathIntervalSource
  CompatibleL1IntervalSource.retardedCriticalPath

/-- The recursive seed uses exactly the original left trace of q. -/
theorem referenceState_left {a b : ℝ} (hab : a ≤ b) (P : Partition a b)
    (q : CriticalPath (intervalMeasure a b)) :
    referenceState P q 0 (Nat.zero_le _) = energyPath _ q ⟨a,le_rfl,hab⟩ := by
  unfold referenceState
  apply congrArg (fun t : Set.Icc a b => energyPath _ q t)
  exact Subtype.ext P.left

/-- The exact original forcing error restricted to the original ith piece. -/
def pieceError {a b : ℝ} (P : Partition a b) (E : CompatibleL1IntervalSource a b) (i : Fin P.count) :
    CompatibleL1IntervalSource (P.time i.castSucc) (P.time i.succ) :=
  E.restrict (P.mem_interval i.castSucc).1 (P.mem_interval i.succ).2

theorem pieceError_gradient_norm_le {a b : ℝ} (P : Partition a b)
    (E : CompatibleL1IntervalSource a b) (i : Fin P.count) :
    ‖(pieceError P E i).gradient‖ ≤ ‖E.gradient‖ :=
  E.restrict_gradient_norm_le (P.mem_interval i.castSucc).1 (P.mem_interval i.succ).2

theorem piece_energy_norm_le {a b : ℝ} (P : Partition a b)
    (q : CriticalPath (intervalMeasure a b)) (i : Fin P.count) :
    ‖energyPath _ (piecePath P q i)‖ ≤ ‖energyPath _ q‖ :=
  restrictPath_energy_norm_le (P.mem_interval i.castSucc).1 (piece_order P i) (P.mem_interval i.succ).2 q

/-- The per-piece mild identity is derived from the same original PDE and source. -/
theorem piece_forced_identity (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
    (hgen : OrdinaryFreeDistributionScalarGenerator) (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hPDE : ForcedHartreeCompactTestIdentity alpha c hab q E)
    (P : Partition a b) (i : Fin P.count) :
    piecePath P q i = hartreeDuhamelMap hDensity hSob h0 hfree hret hH (piece_order P i)
      (referenceState P q i.val i.isLt.le) (piecePath P q i) -
      Complex.I • (pieceError P E i).retardedCriticalPath hDensity hSob h0 hret :=
  actual_restricted_forced_mild_of_distributional hDensity hSob hH hab q E h0 hfree hret hgen hUnique
    hPDE (P.mem_interval i.castSucc).1 (piece_order P i) (P.mem_interval i.succ).2

/-- A real finite recursion constructs every actual solution prefix from the
same q, its original PDE, and the restrictions of its original error. -/
theorem exists_actual_perturbation_prefixes (hDensity : OrdinaryH1Density)
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
      ForcedHartreeCompactTestIdentity alpha c hab q E →
      ‖energyPath _ q‖ ≤ B →
      (∀ i : Fin P.count, ‖fun j => criticalGradient _ j (piecePath P q i)‖ ≤ r) →
      0 ≤ epsilon → ‖f-referenceState P q 0 (Nat.zero_le _)‖ ≤ epsilon → ‖E.gradient‖ ≤ epsilon →
      (iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
        (max (energyEndpointConstant K C0) Cr))^(P.count+1)*epsilon ≤ r/2 →
      ∀ n : ℕ, 1 ≤ n → ∀ hn : n ≤ P.count,
      Nonempty (PrefixSolution hDensity hSob h0 hfree hret hH P f q
        (iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
          (max (energyEndpointConstant K C0) Cr)) epsilon
        (2*C*(iterationMultiplier (max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch)
          (max (energyEndpointConstant K C0) Cr))^P.count*epsilon) n hn) := by
  let choice := exists_actual_solution_fullZ_of_small_forcing hDensity hSob h0 hfree hret hefree heret hH hB
  let r : ℝ := Classical.choose choice
  let cc := Classical.choose_spec choice
  let C : ℝ := Classical.choose cc
  have hs := Classical.choose_spec cc
  have hr : 0 < r := hs.1
  have hC : 0 < C := hs.2.2.1
  refine ⟨r,C,hr,hs.2.1,hC,?_⟩
  intro a b hab f q E P epsilon hPDE hqE hqW heps hf hE hsmall
  let Cf := max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch
  let Q := max (energyEndpointConstant K C0) Cr
  let D := iterationMultiplier Cf Q
  let H := 2*C*D^P.count*epsilon
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hD : 1 ≤ D := iterationMultiplier_one_le hCf hQ
  have hstep (i : Fin P.count) (g : EnergyState)
      (hg : ‖g-referenceState P q i.val i.isLt.le‖ ≤ D^i.val*epsilon) :
      ∃ v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)),
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH (piece_order P i) g v=v ∧
        FullZPath v ∧ ‖v-piecePath P q i‖ ≤ D^(i.val+1)*epsilon ∧
        FullZPath (v-piecePath P q i) ∧ fullZSDifferenceSize v (piecePath P q i) ≤ ENNReal.ofReal H := by
    have he := (pieceError_gradient_norm_le P E i).trans hE
    have hseed := iteration_seed_bounds hCf hQ heps i.isLt hg he hsmall
    let result := hs.2.2.2 (piece_order P i) g (referenceState P q i.val i.isLt.le)
      (piecePath P q i) (pieceError P E i)
      (piece_forced_identity hDensity hSob h0 hfree hret hH hab q E hgen hUnique hPDE P i)
      ((piece_energy_norm_le P q i).trans hqE) (hqW i) hseed.1
    let v : CriticalPath (intervalMeasure (P.time i.castSucc) (P.time i.succ)) := Classical.choose result
    have hv := Classical.choose_spec result
    have hsize := iteration_piece_size_bound hD heps hC.le i.isLt.le hg he
    refine ⟨v,(isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH (piece_order P i) g v).mp hv.1,
      hv.2.1,hv.2.2.2.2.1.trans hseed.2,hv.2.2.1,?_⟩
    exact hv.2.2.2.2.2.1.trans (ENNReal.ofReal_le_ofReal hsize)
  intro n h1
  induction n,h1 using Nat.le_induction with
  | base =>
    intro hn
    let i : Fin P.count := ⟨0,P.positive⟩
    have hg : ‖f-referenceState P q i.val i.isLt.le‖ ≤ D^i.val*epsilon := by
      simpa only [i, pow_zero,one_mul] using hf
    let result := hstep i f hg
    let v := Classical.choose result
    have hv := Classical.choose_spec result
    exact ⟨firstPrefixSolution hDensity hSob h0 hfree hret hH P f q v
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2⟩
  | succ n h1 ih =>
    intro hn
    have hnlt : n < P.count := hn
    let old := Classical.choice (ih hnlt.le)
    let g := energyPath _ old.curve ⟨node P n hnlt.le,P.ordered (Fin.zero_le _),le_rfl⟩
    let i : Fin P.count := ⟨n,hnlt⟩
    let result := hstep i g old.terminal_close
    let v := Classical.choose result
    have hv := Classical.choose_spec result
    exact ⟨appendPrefixSolution hDensity hSob h0 hfree hret hH P f q hnlt old v
      hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2⟩

end HartreeF.FinitePerturbation
