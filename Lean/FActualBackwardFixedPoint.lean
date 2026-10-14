import FActualBackwardHartreeMap
import FActualIntervalSourceBounds
import FLocalFreePathCaps
import FCriticalPathBall
import FSmallRadiusChoice

/-! The finite backward-interval fixed point of the literal Hartree map.
The cap, its nonempty free element, preservation, and contraction are all
produced from the actual estimates. This file is an author draft until a
recorded strict build succeeds; maximal lifespan and scattering are separate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualBackwardLocalFixedPoint
open EnergySpace CriticalPathSpace CriticalPathBall CriticalSourceBounds
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  freeCriticalPath backwardHartreeDuhamelMap criticalPathIntervalSource

/-- Every actual energy datum has a positive backward interval and an actual
fixed point. No interval smallness, source finiteness, self-map estimate,
contraction, or fixed-point datum is an input to this theorem. -/
theorem exists_actual_backward_fixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (b : ℝ) (u0 : EnergyState) :
    ∃ a : ℝ, ∃ hab : a < b, ∃ u : CriticalPath (intervalMeasure a b),
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab.le u0 u = u ∧
      energyPath _ u ⟨b, hab.le, le_rfl⟩ = u0 := by
  let Q := max (energyEndpointConstant K C0) (Ch*C0+Cr)
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  let E0 := (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) * ‖u0‖
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  let B := 2 * E0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let epsilon := 1 / (2 * (Q + 1))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  let smallChoice := criticalPathIntervalSource_cap_uniform_smallness
    hDensity hSob hH hB.le hepsilon
  let rho : ℝ := Classical.choose smallChoice
  have hrho : 0 < rho := (Classical.choose_spec smallChoice).1
  let singleChoice := criticalPathIntervalSource_cap_single_bound hDensity hSob hH
  let C : ℝ≥0 := Classical.choose singleChoice
  have hL : 0 < normComparisonConstant K := normComparisonConstant_pos hSob
  let A := Q * (C : ℝ) * B ^ (2*alpha) * (normComparisonConstant K)^5
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let radiusChoice := exists_small_fifth_power_radius_below A B rho hA hB hrho
  let eta : ℝ := Classical.choose radiusChoice
  have heta : 0 < eta := (Classical.choose_spec radiusChoice).1
  have hetarho : eta ≤ rho := (Classical.choose_spec radiusChoice).2.1
  have hfifth : A * eta^5 ≤ eta/2 := (Classical.choose_spec radiusChoice).2.2.2.2.2.1
  have hfifthB : A * eta^5 ≤ B/16 := (Classical.choose_spec radiusChoice).2.2.2.2.2.2
  let freeChoice := exists_backwardFreeCriticalPath_small
    hDensity hSob hfree b u0 (eta/2) (by positivity)
  let a : ℝ := Classical.choose freeChoice
  have hab : a < b := (Classical.choose_spec freeChoice).1
  let μ := intervalMeasure a b
  let t₀ : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  let free := freeCriticalPath hDensity hSob hfree a b
    (freeEnergyState hDensity hSob (-b) u0)
  let Φ := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab.le u0
  let S := admissiblePaths μ t₀ u0 B eta
  have hfreeE' : ‖energyPath μ free‖ ≤ B/2 := by
    change ‖energyPath _ (freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-b) u0))‖ ≤ B/2
    have hraw : ‖energyPath μ free‖ ≤ E0 := (Classical.choose_spec freeChoice).2.1
    exact hraw.trans (by dsimp [B]; linarith)
  have hfreeIn : free ∈ S := by
    apply admissiblePaths_mem_of_coordinates μ heta.le
    · exact backwardFreeCriticalPath_terminal hDensity hSob hfree hab.le u0
    · exact hfreeE'.trans (by linarith)
    · intro j
      exact ((Classical.choose_spec freeChoice).2.2 j).trans (by linarith)
  have hself : Set.MapsTo Φ S S := by
    intro u hu
    have hG : ‖(criticalPathIntervalSource hDensity hSob hH hab.le u 0).gradient‖ ≤
        (C : ℝ) * B^(2*alpha) * (normComparisonConstant K)^5 * eta^5 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      exact (Classical.choose_spec singleChoice) hab.le u B eta hB.le heta.le hu.2.1 hu.2.2
    have hsource : Q * ‖(criticalPathIntervalSource hDensity hSob hH hab.le u 0).gradient‖ ≤
        A * eta^5 :=
      (mul_le_mul_of_nonneg_left hG hQ).trans_eq (by dsimp [A]; ring)
    apply admissiblePaths_mem_of_coordinates μ heta.le
    · exact backwardHartreeDuhamelMap_terminal hDensity hSob h0 hfree hret hH hab.le u0 u
    · have henergy : energyEndpointConstant K C0 *
          ‖(criticalPathIntervalSource hDensity hSob hH hab.le u 0).gradient‖ ≤ A * eta^5 :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans hsource
      have h := (backwardHartreeDuhamelMap_energy_norm hDensity hSob h0 hfree hret hH
        hab.le u0 u).trans (add_le_add hfreeE' (henergy.trans hfifthB))
      linarith
    · intro j
      have hgradient : (Ch*C0+Cr) * ‖(criticalPathIntervalSource hDensity hSob hH hab.le u 0).gradient j‖ ≤
          A * eta^5 :=
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j) (add_nonneg (mul_nonneg hfree.1 h0.1) hret.1)).trans
          ((mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)).trans hsource)
      exact (backwardHartreeDuhamelMap_gradient_norm hDensity hSob h0 hfree hret hH hab.le u0 u j).trans
        ((add_le_add ((Classical.choose_spec freeChoice).2.2 j) (hgradient.trans hfifth)).trans_eq (by ring))
  have hcontract : ∀ u ∈ S, ∀ v ∈ S, ‖Φ u - Φ v‖ ≤ (1/2 : ℝ)*‖u-v‖ := by
    intro u hu v hv
    have hsrc := (Classical.choose_spec smallChoice).2.2 hab.le u v hu.2.1 hv.2.1
      (hu.2.2.trans hetarho) (hv.2.2.trans hetarho)
    have hdiff := backwardHartreeDuhamelMap_sub_norm_of_gradient_bound hDensity hSob h0
      hfree hret hH hab.le u0 u v hsrc
    have hcoeff : Q * epsilon ≤ (1/2 : ℝ) := by
      dsimp [epsilon]
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : 0 < 2*(Q+1))).mpr
      linarith
    apply hdiff.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (u-v))
  let fixedChoice := exists_unique_fixedPoint_of_bounds μ t₀ u0 B eta Φ
    ⟨free, hfreeIn⟩ hself hcontract
  let u : CriticalPath μ := Classical.choose fixedChoice
  have hu : u ∈ S := (Classical.choose_spec fixedChoice).1
  have hfix : Φ u = u := (Classical.choose_spec fixedChoice).2.1
  exact ⟨a, hab, u, hfix, hu.1⟩

end HartreeF.ActualBackwardLocalFixedPoint
