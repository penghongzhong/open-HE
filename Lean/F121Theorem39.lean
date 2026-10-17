import FPaperNormCompactPerturbation
import FPaperNormBackwardCompactPerturbation

/-! Literal terminal wrapper for Theorem 3.9 of the 121-page manuscript.
One threshold and one constant, chosen before the interval and all path data,
control both the initial-data and terminal-data perturbation statements in the
paper's E+W+Z+S sum and pointwise homogeneous energy norm. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121Theorem39
open EnergySpace CriticalPathSpace ActualDuhamelPath ActualPerturbation
open CriticalSourceBounds
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
open HomogeneousStability EssentialEnergyCap TimeHolder PaperNormCompactPerturbation
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  CriticalJointSources.jointFields fullZSDifferenceSize paperZSDifferenceSize
  ForcedHartreeCompactTestIdentity IsMildHartreePath IsBackwardMildHartreePath FullZPath
  energyComplexGradient pureGradientNorm pathValueSize mixedNorm
  CompatibleL1IntervalSource.paperForcingSize

/-- The complete forward conclusion of the manuscript's perturbation bound. -/
def ForwardPerturbationResult {a b : ℝ} (hab : a ≤ b) (alpha kernel : ℝ)
    (f : EnergyState) (q : CriticalPath (intervalMeasure a b)) (C epsilon : ℝ)
    (u : CriticalPath (intervalMeasure a b)) : Prop :=
  IsMildHartreePath hab alpha kernel f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
  energyPath _ u ⟨a,le_rfl,hab⟩ = f ∧
  (∀ t, pureGradientNorm (energyPath _ (u-q) t) ≤ C*epsilon) ∧
  paperZSDifferenceSize u q ≤ ENNReal.ofReal (C*epsilon) ∧
  ∀ v : CriticalPath (intervalMeasure a b), IsMildHartreePath hab alpha kernel f v → v=u

/-- The complete terminal-data conclusion, with the advanced mild formula. -/
def BackwardPerturbationResult {a b : ℝ} (hab : a ≤ b) (alpha kernel : ℝ)
    (f : EnergyState) (q : CriticalPath (intervalMeasure a b)) (C epsilon : ℝ)
    (u : CriticalPath (intervalMeasure a b)) : Prop :=
  IsBackwardMildHartreePath hab alpha kernel f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
  energyPath _ u ⟨b,hab,le_rfl⟩ = f ∧
  (∀ t, pureGradientNorm (energyPath _ (u-q) t) ≤ C*epsilon) ∧
  paperZSDifferenceSize u q ≤ ENNReal.ofReal (C*epsilon) ∧
  ∀ v : CriticalPath (intervalMeasure a b),
    IsBackwardMildHartreePath hab alpha kernel f v → v=u

theorem forwardPerturbationResult_mono {a b alpha kernel C D epsilon : ℝ}
    (hab : a ≤ b) (f : EnergyState) (q u : CriticalPath (intervalMeasure a b))
    (hepsilon : 0 ≤ epsilon) (hCD : C ≤ D)
    (h : ForwardPerturbationResult hab alpha kernel f q C epsilon u) :
    ForwardPerturbationResult hab alpha kernel f q D epsilon u := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun t => (h.2.2.2.2.1 t).trans (mul_le_mul_of_nonneg_right hCD hepsilon),
    h.2.2.2.2.2.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCD hepsilon)), h.2.2.2.2.2.2⟩

theorem backwardPerturbationResult_mono {a b alpha kernel C D epsilon : ℝ}
    (hab : a ≤ b) (f : EnergyState) (q u : CriticalPath (intervalMeasure a b))
    (hepsilon : 0 ≤ epsilon) (hCD : C ≤ D)
    (h : BackwardPerturbationResult hab alpha kernel f q C epsilon u) :
    BackwardPerturbationResult hab alpha kernel f q D epsilon u := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    fun t => (h.2.2.2.2.1 t).trans (mul_le_mul_of_nonneg_right hCD hepsilon),
    h.2.2.2.2.2.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCD hepsilon)), h.2.2.2.2.2.2⟩

/-- Theorem 3.9, including its terminal-data clause.  The essential energy
cap is used only on a positive-length interval, so continuity recovers both
endpoint states.  `paperZSDifferenceSize` is exactly the manuscript's sum
`E_I + W_I + Z_I + S_I` on the same actual representatives. -/
theorem theorem39_interval_independent_perturbation
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < C ∧
      ∀ {a b epsilon : ℝ} (hab : a < b)
      (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b),
      ForcedHartreeCompactTestIdentity alpha kernel hab.le q E →
      mixedNorm (intervalMeasure a b) volume ∞ 2
        (fun t => energyComplexGradient (energyPath _ q t)) ≤ ENNReal.ofReal B →
      mixedNorm (intervalMeasure a b) volume 10 10
        (fun t => energyValue (energyPath _ q t)) ≤ ENNReal.ofReal M →
      0 ≤ epsilon → epsilon ≤ epsilon0 →
      E.paperForcingSize ≤ ENNReal.ofReal epsilon →
      (∀ f : EnergyState,
        pureGradientNorm (f-energyPath _ q ⟨a,le_rfl,hab.le⟩) ≤ epsilon →
        ∃ u : CriticalPath (intervalMeasure a b),
          ForwardPerturbationResult hab.le alpha kernel f q C epsilon u) ∧
      (∀ f : EnergyState,
        pureGradientNorm (f-energyPath _ q ⟨b,hab.le,le_rfl⟩) ≤ epsilon →
        ∃ u : CriticalPath (intervalMeasure a b),
          BackwardPerturbationResult hab.le alpha kernel f q C epsilon u) := by
  let forwardChoice := exists_paper_norm_uniform_compact_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB hM
  let epsilonF : ℝ := Classical.choose forwardChoice
  let forwardConstants := Classical.choose_spec forwardChoice
  let CF : ℝ := Classical.choose forwardConstants
  have hforward := Classical.choose_spec forwardConstants
  let backwardChoice := exists_paper_norm_uniform_backward_compact_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB hM
  let epsilonB : ℝ := Classical.choose backwardChoice
  let backwardConstants := Classical.choose_spec backwardChoice
  let CB : ℝ := Classical.choose backwardConstants
  have hbackward := Classical.choose_spec backwardConstants
  refine ⟨min epsilonF epsilonB, max CF CB, lt_min hforward.1 hbackward.1,
    (min_le_left _ _).trans hforward.2.1,
    hforward.2.2.1.trans_le (le_max_left _ _), ?_⟩
  intro a b epsilon hab q E hPDE hE hS hepsilon hepsilonSmall herr
  constructor
  · intro f hf
    obtain ⟨u, hu, huZ, hdiffZ, htrace, hpoint, hsum, huniq⟩ :=
      hforward.2.2.2 hab f q E hPDE hE hS hepsilon
        (hepsilonSmall.trans (min_le_left _ _)) hf herr
    refine ⟨u, forwardPerturbationResult_mono hab.le f q u hepsilon
      (le_max_left CF CB) ?_⟩
    exact ⟨hu, huZ, hdiffZ, htrace, hpoint, hsum, huniq⟩
  · intro f hf
    obtain ⟨u, hu, huZ, hdiffZ, htrace, hpoint, hsum, huniq⟩ :=
      hbackward.2.2.2 hab f q E hPDE hE hS hepsilon
        (hepsilonSmall.trans (min_le_right _ _)) hf herr
    refine ⟨u, backwardPerturbationResult_mono hab.le f q u hepsilon
      (le_max_right CF CB) ?_⟩
    exact ⟨hu, huZ, hdiffZ, htrace, hpoint, hsum, huniq⟩

#print axioms theorem39_interval_independent_perturbation
end HartreeF.Paper121Theorem39
