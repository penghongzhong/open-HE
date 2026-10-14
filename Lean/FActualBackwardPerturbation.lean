import FActualHartreePerturbation
import FActualBackwardLocalComparison
import FBackwardMildHartreeDefinition
import FActualBackwardPathUniqueness
import FActualBackwardMildSolution

/-! A small perturbation of the literal Hartree Duhamel map about an actual
critical path. The radius, self-map and contraction follow from the accepted
Hartree source estimate. The error seed is a genuine path; its later PDE
realization and long-time iteration are separate consumers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped NNReal Topology
namespace HartreeF.BackwardPerturbation
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalPathBall LocalSolutionComparison ActualPerturbation BackwardSolutionComparison
open CriticalUniqueness ActualBackwardLocalFixedPoint EndpointOutput
local instance canonicalEnergyNormedSpace : NormedSpace ℂ EnergyState :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := EnergyAmbient) energySubmodule
local instance canonicalPathNormedSpace (a b : ℝ) :
    NormedSpace ℂ (CriticalPath (intervalMeasure a b)) :=
  Submodule.normedSpace (𝕜 := ℂ) (R := ℂ) (E := PathAmbient (intervalMeasure a b))
    (criticalPathSubmodule (intervalMeasure a b))
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient backwardHartreeDuhamelMap criticalPathIntervalSource

/-- Uniform small-W perturbation construction. Neither a self-map nor a
contraction estimate is an input; both are produced for the actual nonlinearity.
The quantitative output is the genuine E+W path norm. -/
theorem exists_actual_backward_small_perturbation (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f : EnergyState) (q d : CriticalPath (intervalMeasure a b)),
      ‖energyPath _ q‖ ≤ B →
      ‖fun j => criticalGradient _ j q‖ ≤ r → ‖d‖ ≤ r/2 →
      ∃ w : CriticalPath (intervalMeasure a b), ‖w‖ ≤ r ∧
        d + (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f (q+w) -
          backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f q) = w ∧
        ‖w‖ ≤ 2 * ‖d‖ := by
  let choice := exists_actual_backward_source_smallness_and_contraction
    hDensity hSob h0 hfree hret hH (B := B+1) (by linarith)
  let rho : ℝ := Classical.choose choice
  have hrho : 0 < rho := (Classical.choose_spec choice).1
  have hrho1 : rho ≤ 1 := (Classical.choose_spec choice).2.1
  let r := rho/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  refine ⟨r, hr, hr1, ?_⟩
  intro a b hab f q d hqE hqW hd
  let Φ := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f
  let N := fun w => Φ (q+w)-Φ q
  have hzero : N 0 = 0 := by
    dsimp only [N, Φ]
    rw [add_zero]
    exact sub_self (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f q)
  have hE (w : CriticalPath (intervalMeasure a b)) (hw : ‖w‖ ≤ r) :
      ‖energyPath _ (q+w)‖ ≤ B+1 := by
    rw [map_add]
    have hn := norm_add_le (energyPath (intervalMeasure a b) q)
      (energyPath (intervalMeasure a b) w)
    have hwE : ‖energyPath (intervalMeasure a b) w‖ ≤ 1 :=
      (energyPath_norm_le _ w).trans (hw.trans hr1)
    exact hn.trans (add_le_add hqE hwE)
  have hW (w : CriticalPath (intervalMeasure a b)) (hw : ‖w‖ ≤ r) :
      ‖fun j => criticalGradient _ j (q+w)‖ ≤ rho := by
    apply (pi_norm_le_iff_of_nonneg hrho.le).mpr
    intro j
    have hqj := (norm_le_pi_norm (fun j => criticalGradient _ j q) j).trans hqW
    have hwj := (criticalGradient_norm_le _ w j).trans hw
    rw [map_add]
    have hn := norm_add_le (criticalGradient _ j q) (criticalGradient _ j w)
    dsimp [r] at hqj hwj
    linarith
  have hc : ∀ w, ‖w‖ ≤ r → ∀ v, ‖v‖ ≤ r →
      ‖N w - N v‖ ≤ (1/2 : ℝ) * ‖w-v‖ := by
    intro w hw v hv
    have h := ((Classical.choose_spec choice).2.2 hab f (q+w) (q+v) (hE w hw) (hE v hv) (hW w hw) (hW v hv)).2
    have hn : N w - N v =
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f (q+w) -
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f (q+v) := by
      dsimp only [N, Φ]
      exact sub_sub_sub_cancel_right
        (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f (q+w))
        (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f (q+v))
        (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f q)
    have ha : q+w-(q+v) = w-v := add_sub_add_left_eq_sub w v q
    exact (congrArg norm hn).trans_le
      (h.trans_eq (congrArg (fun x : CriticalPath (intervalMeasure a b) => (1/2 : ℝ)*‖x‖) ha))
  exact exists_small_increment_fixedPoint N d hr.le hd hzero hc

#print axioms exists_actual_backward_small_perturbation
end HartreeF.BackwardPerturbation
