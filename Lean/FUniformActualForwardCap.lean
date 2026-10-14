import FActualLocalFixedPoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.UniformLocalData
open EnergySpace CriticalPathSpace CriticalPathBall CriticalSourceBounds
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain
attribute [local irreducible] energySubmodule criticalPathSubmodule
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource

/-- The nonlinear cap radius is produced before the interval and datum. Once
that datum's literal free path obeys the displayed quantitative caps, the
actual map produces a fixed point in the same cap. No source estimate,
self-map property, contraction or nonlinear solution is an input. -/
theorem exists_uniform_actual_forward_cap (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B rho0 : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hB : 0 < B) (hrho0 : 0 < rho0) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ rho0 ∧ ∀ {a b : ℝ} (hab : a ≤ b) (u0 : EnergyState),
      ‖energyPath (intervalMeasure a b)
        (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0))‖ ≤ B/2 →
      (∀ j : Fin 3, ‖criticalGradient (intervalMeasure a b) j
        (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) u0))‖ ≤ eta/2) →
      ∃ u : CriticalPath (intervalMeasure a b),
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u ∧
        energyPath _ u ⟨a, le_rfl, hab⟩ = u0 ∧
        ‖energyPath _ u‖ ≤ B ∧ ‖gradientCoordinates _ u‖ ≤ eta := by
  let Q := max (energyEndpointConstant K C0) Cr
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
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
  let radiusChoice := exists_small_fifth_power_radius_below A B (min rho rho0)
    hA hB (lt_min hrho hrho0)
  let eta : ℝ := Classical.choose radiusChoice
  have heta : 0 < eta := (Classical.choose_spec radiusChoice).1
  have hetarho : eta ≤ rho := (Classical.choose_spec radiusChoice).2.1.trans (min_le_left _ _)
  have hetarho0 : eta ≤ rho0 := (Classical.choose_spec radiusChoice).2.1.trans (min_le_right _ _)
  have hfifth : A * eta^5 ≤ eta/2 := (Classical.choose_spec radiusChoice).2.2.2.2.2.1
  have hfifthB : A * eta^5 ≤ B/16 := (Classical.choose_spec radiusChoice).2.2.2.2.2.2
  refine ⟨eta, heta, hetarho0, ?_⟩
  intro a b hab u0 hfreeE' hfreeW
  let μ := intervalMeasure a b
  let t₀ : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let free := freeCriticalPath hDensity hSob hfree a b
    (freeEnergyState hDensity hSob (-a) u0)
  let Φ := hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0
  let S := admissiblePaths μ t₀ u0 B eta
  have hfreeIn : free ∈ S := by
    apply admissiblePaths_mem_of_coordinates μ heta.le
    · exact shiftedFreeCriticalPath_initial hDensity hSob hfree hab u0
    · exact hfreeE'.trans (by linarith)
    · intro j
      exact (hfreeW j).trans (by linarith)
  have hself : Set.MapsTo Φ S S := by
    intro u hu
    have hG : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤
        (C : ℝ) * B^(2*alpha) * (normComparisonConstant K)^5 * eta^5 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      exact (Classical.choose_spec singleChoice) hab u B eta hB.le heta.le hu.2.1 hu.2.2
    have hsource : Q * ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤
        A * eta^5 :=
      (mul_le_mul_of_nonneg_left hG hQ).trans_eq (by dsimp [A]; ring)
    apply admissiblePaths_mem_of_coordinates μ heta.le
    · exact hartreeDuhamelMap_initial hDensity hSob h0 hfree hret hH hab u0 u
    · have henergy : energyEndpointConstant K C0 *
          ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤ A * eta^5 :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans hsource
      have h := (hartreeDuhamelMap_energy_norm hDensity hSob h0 hfree hret hH
        hab u0 u).trans (add_le_add hfreeE' (henergy.trans hfifthB))
      linarith
    · intro j
      have hgradient : Cr * ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j‖ ≤
          A * eta^5 :=
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j) hret.1).trans
          ((mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)).trans hsource)
      exact (hartreeDuhamelMap_gradient_norm hDensity hSob h0 hfree hret hH hab u0 u j).trans
        ((add_le_add (hfreeW j) (hgradient.trans hfifth)).trans_eq (by ring))
  have hcontract : ∀ u ∈ S, ∀ v ∈ S, ‖Φ u - Φ v‖ ≤ (1/2 : ℝ)*‖u-v‖ := by
    intro u hu v hv
    have hsrc := (Classical.choose_spec smallChoice).2.2 hab u v hu.2.1 hv.2.1
      (hu.2.2.trans hetarho) (hv.2.2.trans hetarho)
    have hdiff := hartreeDuhamelMap_sub_norm_of_gradient_bound hDensity hSob h0
      hfree hret hH hab u0 u v hsrc
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
  exact ⟨u, hfix, hu.1, hu.2.1, hu.2.2⟩

end HartreeF.UniformLocalData
