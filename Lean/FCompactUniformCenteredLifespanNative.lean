import FCompactUniformFreeCapsNative
import FUniformForwardInitialSolver
import FUniformBackwardTerminalSolver
import FLocalMildTrajectoryExistence

/-! Native compact-carrier uniform centered lifespan, constructed from actual
forward/backward fixed points. AUTHOR CANDIDATE; NOT COMPILED.
Only six of the original eight ordinary analytic premises are needed here.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.CompactUniformLifespan
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
open CriticalPathRestriction CriticalPathGluing CriticalUniqueness MaximalTrajectory
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalGradient freeCriticalPath freeEnergyState hartreeDuhamelMap
  backwardHartreeDuhamelMap criticalPathIntervalSource restrictPath gluePath
  CriticalUniqueness.IsMildHartreePath CriticalUniqueness.IsBackwardMildHartreePath

/-- The zero anchoring equality is transported as a typed path equality. -/
private theorem free_zero_anchor_path_eq (hD : OrdinaryH1Density)
    {K Ch : ℝ} (hS : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (q : EnergyState) :
    freeCriticalPath hD hS hfree a b (freeEnergyState hD hS (-0) q) =
      freeCriticalPath hD hS hfree a b q := by
  have hz : freeEnergyState hD hS (-0) q = q := by
    simpa only [neg_zero] using freeEnergyState_zero_time hD hS q
  exact congrArg (fun z : EnergyState => freeCriticalPath hD hS hfree a b z) hz

/-- Thin zero-centered interface of the existing actual forward solver.
Unused error/cap outputs stay inside this helper, outside the compact proof. -/
private theorem uniform_forward_zero_radius (hD : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B : ℝ} (hS : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hB : 0 < B) :
    ∃ η : ℝ, 0 < η ∧ ∀ (b : ℝ) (hb : 0 ≤ b) (q : EnergyState),
      ‖energyPath _ (freeCriticalPath hD hS hfree 0 b q)‖ ≤ B / 2 →
      (∀ j : Fin 3, ‖criticalGradient _ j (freeCriticalPath hD hS hfree 0 b q)‖ ≤ η / 2) →
      ∃ u : CriticalPath (intervalMeasure 0 b),
        hartreeDuhamelMap hD hS h0 hfree hret hH hb q u = u ∧
        energyPath _ u ⟨0, le_rfl, hb⟩ = q := by
  let e := WaveInitial.exists_uniform_forward_initial_radius hD hS h0 hfree hret hH
    (B := B) (delta := 1) hB (by norm_num)
  let η : ℝ := Classical.choose e
  have hη : 0 < η := (Classical.choose_spec e).1
  refine ⟨η, hη, ?_⟩
  intro b hb q hE hW
  have heq := free_zero_anchor_path_eq hD hS hfree 0 b q
  have hEeq : ‖energyPath _ (freeCriticalPath hD hS hfree 0 b
      (freeEnergyState hD hS (-0) q))‖ =
      ‖energyPath _ (freeCriticalPath hD hS hfree 0 b q)‖ :=
    congrArg (fun z : CriticalPath (intervalMeasure 0 b) =>
      ‖energyPath (intervalMeasure 0 b) z‖) heq
  have hWshift (j : Fin 3) : ‖criticalGradient _ j (freeCriticalPath hD hS hfree 0 b
      (freeEnergyState hD hS (-0) q))‖ ≤ η / 2 :=
    (congrArg (fun z : CriticalPath (intervalMeasure 0 b) =>
      ‖criticalGradient (intervalMeasure 0 b) j z‖) heq).le.trans (hW j)
  let solved := (Classical.choose_spec e).2.2 hb q
    (hEeq.le.trans hE) hWshift
  let u : CriticalPath (intervalMeasure 0 b) := Classical.choose solved
  exact ⟨u, (Classical.choose_spec solved).1, (Classical.choose_spec solved).2.1⟩

/-- Thin zero-centered interface of the existing actual backward solver. -/
private theorem uniform_backward_zero_radius (hD : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B : ℝ} (hS : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hB : 0 < B) :
    ∃ η : ℝ, 0 < η ∧ ∀ (a : ℝ) (ha : a ≤ 0) (q : EnergyState),
      ‖energyPath _ (freeCriticalPath hD hS hfree a 0 q)‖ ≤ B / 2 →
      (∀ j : Fin 3, ‖criticalGradient _ j (freeCriticalPath hD hS hfree a 0 q)‖ ≤ η / 2) →
      ∃ u : CriticalPath (intervalMeasure a 0),
        backwardHartreeDuhamelMap hD hS h0 hfree hret hH ha q u = u ∧
        energyPath _ u ⟨0, ha, le_rfl⟩ = q := by
  let e := WaveTerminal.exists_uniform_backward_terminal_radius hD hS h0 hfree hret hH
    (B := B) (delta := 1) hB (by norm_num)
  let η : ℝ := Classical.choose e
  have hη : 0 < η := (Classical.choose_spec e).1
  refine ⟨η, hη, ?_⟩
  intro a ha q hE hW
  have heq := free_zero_anchor_path_eq hD hS hfree a 0 q
  have hEeq : ‖energyPath _ (freeCriticalPath hD hS hfree a 0
      (freeEnergyState hD hS (-0) q))‖ =
      ‖energyPath _ (freeCriticalPath hD hS hfree a 0 q)‖ :=
    congrArg (fun z : CriticalPath (intervalMeasure a 0) =>
      ‖energyPath (intervalMeasure a 0) z‖) heq
  have hWshift (j : Fin 3) : ‖criticalGradient _ j (freeCriticalPath hD hS hfree a 0
      (freeEnergyState hD hS (-0) q))‖ ≤ η / 2 :=
    (congrArg (fun z : CriticalPath (intervalMeasure a 0) =>
      ‖criticalGradient (intervalMeasure a 0) j z‖) heq).le.trans (hW j)
  let solved := (Classical.choose_spec e).2.2 ha q
    (hEeq.le.trans hE) hWshift
  let u : CriticalPath (intervalMeasure a 0) := Classical.choose solved
  exact ⟨u, (Classical.choose_spec solved).1, (Classical.choose_spec solved).2.1⟩

/-- Actual adjacent fixed points give an actual centered whole mild path.
Only the two restriction equalities are transported; mild predicates stay opaque. -/
private theorem whole_path_of_zero_fixedPoints (hD : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hS : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (ha : a ≤ 0) (hb : 0 ≤ b) (q : EnergyState)
    (l : CriticalPath (intervalMeasure a 0)) (r : CriticalPath (intervalMeasure 0 b))
    (hlfixed : backwardHartreeDuhamelMap hD hS h0 hfree hret hH ha q l = l)
    (hlterminal : energyPath _ l ⟨0, ha, le_rfl⟩ = q)
    (hrfixed : hartreeDuhamelMap hD hS h0 hfree hret hH hb q r = r)
    (hrinitial : energyPath _ r ⟨0, le_rfl, hb⟩ = q) :
    ∃ u : CriticalPath (intervalMeasure a b),
      energyPath _ u ⟨0, ha, hb⟩ = q ∧
      IsMildHartreePath (ha.trans hb) alpha kernel
        (energyPath _ u ⟨a, le_rfl, ha.trans hb⟩) u := by
  have hmatch : energyPath _ l ⟨0, ha, le_rfl⟩ =
      energyPath _ r ⟨0, le_rfl, hb⟩ := hlterminal.trans hrinitial.symm
  let u : CriticalPath (intervalMeasure a b) := gluePath ha hb l r hmatch
  have hcenter : energyPath _ u ⟨0, ha, hb⟩ = q :=
    (gluePath_middle ha hb l r hmatch).trans hlterminal
  have hLmild : IsBackwardMildHartreePath ha alpha kernel q l :=
    (isBackwardMildHartreePath_iff_fixedPoint hD hS h0 hfree hret hH ha q l).mpr hlfixed
  have hRmild : IsMildHartreePath hb alpha kernel q r :=
    (isMildHartreePath_iff_fixedPoint hD hS h0 hfree hret hH hb q r).mpr hrfixed
  have hLrestrict : IsBackwardMildHartreePath ha alpha kernel q
      (restrictPath le_rfl ha hb u) :=
    Eq.mpr (congrArg (fun z : CriticalPath (intervalMeasure a 0) =>
      IsBackwardMildHartreePath ha alpha kernel q z)
      (restrict_gluePath_left ha hb l r hmatch)) hLmild
  have hRrestrict : IsMildHartreePath hb alpha kernel q
      (restrictPath ha hb le_rfl u) :=
    Eq.mpr (congrArg (fun z : CriticalPath (intervalMeasure 0 b) =>
      IsMildHartreePath hb alpha kernel q z)
      (restrict_gluePath_right ha hb l r hmatch)) hRmild
  exact ⟨u, hcenter, centered_mild_is_forward_mild hD hS h0 hfree hret hH
    ha hb q u hLrestrict hRrestrict⟩

/-- One actual whole mild path interval serves every datum in the compact carrier.
The energy bound is chosen before the two nonlinear radii; only then is the
uniform free window chosen from compactness. -/
theorem exists_compact_uniform_centered_mild_path (hD : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ} (hS : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {Q : Set EnergyState} (hQ : IsCompact Q) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∀ q ∈ Q,
      ∃ u : CriticalPath (intervalMeasure (-δ) δ),
        energyPath _ u ⟨0, by linarith, hδ.le⟩ = q ∧
        IsMildHartreePath (by linarith : -δ ≤ δ) alpha kernel
          (energyPath _ u ⟨-δ, le_rfl, by linarith⟩) u := by
  let energyChoice := compact_uniform_freeEnergy_cap hD hS hfree hQ
  let B : ℝ := Classical.choose energyChoice
  have hB : 0 < B := (Classical.choose_spec energyChoice).1
  have henergy (a b : ℝ) (q : EnergyState) (hq : q ∈ Q) :
      ‖energyPath _ (freeCriticalPath hD hS hfree a b q)‖ ≤ B / 2 :=
    (Classical.choose_spec energyChoice).2 a b q hq
  let forwardChoice := uniform_forward_zero_radius hD hS h0 hfree hret hH (B := B) hB
  let ηF : ℝ := Classical.choose forwardChoice
  have hηF : 0 < ηF := (Classical.choose_spec forwardChoice).1
  have hforward := (Classical.choose_spec forwardChoice).2
  let backwardChoice := uniform_backward_zero_radius hD hS h0 hfree hret hH (B := B) hB
  let ηB : ℝ := Classical.choose backwardChoice
  have hηB : 0 < ηB := (Classical.choose_spec backwardChoice).1
  have hbackward := (Classical.choose_spec backwardChoice).2
  let η : ℝ := min (ηF / 2) (ηB / 2)
  have hη : 0 < η := lt_min (half_pos hηF) (half_pos hηB)
  let windowChoice := compact_uniform_freeGradient_small hD hS hfree hQ hη
  let δ : ℝ := Classical.choose windowChoice
  have hδ : 0 < δ := (Classical.choose_spec windowChoice).1
  have hgradient (a b : ℝ) (ha : -δ ≤ a) (hb : b ≤ δ)
      (q : EnergyState) (hq : q ∈ Q) (j : Fin 3) :
      ‖criticalGradient _ j (freeCriticalPath hD hS hfree a b q)‖ ≤ η :=
    (Classical.choose_spec windowChoice).2 a b ha hb q hq j
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have hleft : -δ ≤ 0 := by linarith
  have hright : 0 ≤ δ := hδ.le
  have hFW (j : Fin 3) :
      ‖criticalGradient _ j (freeCriticalPath hD hS hfree 0 δ q)‖ ≤ ηF / 2 :=
    (hgradient 0 δ hleft le_rfl q hq j).trans (min_le_left (ηF / 2) (ηB / 2))
  have hBW (j : Fin 3) :
      ‖criticalGradient _ j (freeCriticalPath hD hS hfree (-δ) 0 q)‖ ≤ ηB / 2 :=
    (hgradient (-δ) 0 le_rfl hright q hq j).trans (min_le_right (ηF / 2) (ηB / 2))
  let rightChoice := hforward δ hright q (henergy 0 δ q hq) hFW
  let r : CriticalPath (intervalMeasure 0 δ) := Classical.choose rightChoice
  have hrfixed : hartreeDuhamelMap hD hS h0 hfree hret hH hright q r = r :=
    (Classical.choose_spec rightChoice).1
  have hrinitial : energyPath _ r ⟨0, le_rfl, hright⟩ = q :=
    (Classical.choose_spec rightChoice).2
  let leftChoice := hbackward (-δ) hleft q (henergy (-δ) 0 q hq) hBW
  let l : CriticalPath (intervalMeasure (-δ) 0) := Classical.choose leftChoice
  have hlfixed : backwardHartreeDuhamelMap hD hS h0 hfree hret hH hleft q l = l :=
    (Classical.choose_spec leftChoice).1
  have hlterminal : energyPath _ l ⟨0, hleft, le_rfl⟩ = q :=
    (Classical.choose_spec leftChoice).2
  exact whole_path_of_zero_fixedPoints hD hS h0 hfree hret hH
    hleft hright q l r hlfixed hlterminal hrfixed hrinitial

/-- The actual local trajectory domains contain one common closed centered window.
The half-window lies strictly inside the constructed open domain, retaining the
strict inclusion needed by the finite-endpoint collapse argument. -/
theorem exists_compact_uniform_centered_lifespan (hD : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ} (hS : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {Q : Set EnergyState} (hQ : IsCompact Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ Q,
      ∃ u : LocalMildTrajectory alpha kernel 0 q, Set.Icc (-δ) δ ⊆ u.domain := by
  obtain ⟨r, hr, hpaths⟩ := exists_compact_uniform_centered_mild_path
    hD hS h0 hfree hret hH hQ
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro q hq
  obtain ⟨u, hcenter, hmild⟩ := hpaths q hq
  have hl : -r < 0 := by linarith
  let v : LocalMildTrajectory alpha kernel 0 q :=
    localTrajectoryOfCenteredPath hD hS h0 hfree hret hH hl hr q u hcenter hmild
  refine ⟨v, ?_⟩
  intro t ht
  change t ∈ Set.Ioo (-r) r
  constructor <;> linarith [ht.1, ht.2]

#print axioms exists_compact_uniform_centered_mild_path
#print axioms exists_compact_uniform_centered_lifespan
end HartreeF.CompactUniformLifespan
