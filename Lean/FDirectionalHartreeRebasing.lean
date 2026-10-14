import FFreeCriticalPathRebase

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open EnergySpace CriticalPathSpace IntervalTimeTransport Retarded
open SobolevStretch StationarySelfTest ActualStrichartz ForcingDomain
local instance directionalEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance directionalGraphNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath freeEnergyState criticalPathIntervalSource intervalRetardedCriticalPath
  intervalTotalSourceEnergy hartreeDuhamelMap backwardHartreeDuhamelMap
  intervalAdvancedCriticalPath

/-- Rebase the actual forward Phi at its actual terminal energy. Both directions
use the same input u and its literal Hartree source on the same full graph space. -/
theorem backwardHartreeDuhamelMap_forward_terminal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u)
        ⟨b,hab,le_rfl⟩) u = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u := by
  let F := criticalPathIntervalSource hDensity hSob hH hab u 0
  let R := intervalRetardedCriticalPath hDensity hSob h0 hret F
  let Q := freeCriticalPath hDensity hSob hfree a b (intervalTotalSourceEnergy hDensity hSob h0 F)
  let X := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0)
  let P := criticalPathFreeRebase hDensity hSob hfree (⟨b,hab,le_rfl⟩ : Set.Icc a b)
  have hX : P X = X := criticalPathFreeRebase_free hDensity hSob hfree _ _
  have hQ : P Q = Q := criticalPathFreeRebase_free hDensity hSob hfree _ _
  have hA : P (Q-R) = 0 := by
    apply criticalPathFreeRebase_of_energy_zero hDensity hSob hfree _ (Q-R)
    have he := intervalAdvancedCriticalPath_terminal hDensity hSob h0 hfree hret hab F
    unfold intervalAdvancedCriticalPath at he
    exact he
  have hAlg := rebase_forward_algebra (G := CriticalPath (intervalMeasure a b)) P X Q R hX hQ hA
  unfold backwardHartreeDuhamelMap hartreeDuhamelMap intervalAdvancedCriticalPath
  exact hAlg

/-- Rebase the actual backward Phi at its actual initial energy, keeping exactly
the same u and actual Hartree source. No additional integration estimate enters. -/
theorem hartreeDuhamelMap_backward_initial (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u)
        ⟨a,le_rfl,hab⟩) u = backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u := by
  let F := criticalPathIntervalSource hDensity hSob hH hab u 0
  let R := intervalRetardedCriticalPath hDensity hSob h0 hret F
  let Q := freeCriticalPath hDensity hSob hfree a b (intervalTotalSourceEnergy hDensity hSob h0 F)
  let X := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
  let P := criticalPathFreeRebase hDensity hSob hfree (⟨a,le_rfl,hab⟩ : Set.Icc a b)
  have hX : P X = X := criticalPathFreeRebase_free hDensity hSob hfree _ _
  have hQ : P Q = Q := criticalPathFreeRebase_free hDensity hSob hfree _ _
  have hR : P R = 0 := by
    apply criticalPathFreeRebase_of_energy_zero hDensity hSob hfree _ R
    exact intervalRetardedCriticalPath_initial hDensity hSob h0 hret hab F
  have hAlg := rebase_backward_algebra (G := CriticalPath (intervalMeasure a b)) P X Q R hX hQ hR
  unfold hartreeDuhamelMap backwardHartreeDuhamelMap intervalAdvancedCriticalPath
  exact hAlg

/-- A forward fixed point is a backward fixed point with its actual terminal data. -/
theorem forwardFixedPoint_is_backward_at_terminal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b))
    (hfix : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u) :
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ u ⟨b,hab,le_rfl⟩) u = u := by
  have he := backwardHartreeDuhamelMap_forward_terminal hDensity hSob h0 hfree hret hH hab u0 u
  let D : CriticalPath (intervalMeasure a b) → CriticalPath (intervalMeasure a b) :=
    fun v => backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ v ⟨b,hab,le_rfl⟩) u
  exact (congrArg D hfix).symm.trans (he.trans hfix)

/-- A backward fixed point is a forward fixed point with its actual initial data. -/
theorem backwardFixedPoint_is_forward_at_initial (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u : CriticalPath (intervalMeasure a b))
    (hfix : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u = u) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ u ⟨a,le_rfl,hab⟩) u = u := by
  have he := hartreeDuhamelMap_backward_initial hDensity hSob h0 hfree hret hH hab ub u
  let D : CriticalPath (intervalMeasure a b) → CriticalPath (intervalMeasure a b) :=
    fun v => hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ v ⟨a,le_rfl,hab⟩) u
  exact (congrArg D hfix).symm.trans (he.trans hfix)

/-- Same-curve directional equivalence uses the curve's own two endpoint values. -/
theorem actualEndpoint_fixedPoint_iff (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (u : CriticalPath (intervalMeasure a b)) :
    (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ u ⟨a,le_rfl,hab⟩) u = u) ↔
    (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ u ⟨b,hab,le_rfl⟩) u = u) := by
  constructor
  · exact forwardFixedPoint_is_backward_at_terminal hDensity hSob h0 hfree hret hH hab _ u
  · exact backwardFixedPoint_is_forward_at_initial hDensity hSob h0 hfree hret hH hab _ u

end HartreeF.ActualDuhamelPath
