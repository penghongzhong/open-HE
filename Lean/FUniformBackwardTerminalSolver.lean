import FActualBackwardPathUniqueness
import FActualFreePathDifference
import FSmallRadiusChoice

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.WaveTerminal
open EnergySpace CriticalPathSpace CriticalPathBall CriticalSourceBounds
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain BackwardSolutionComparison
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  freeCriticalPath backwardHartreeDuhamelMap criticalPathIntervalSource energyPath

private theorem norm_decrement_sub_free {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x y : E) : ‖(x-Complex.I • y)-x‖=‖y‖ := by
  have he : (x-Complex.I • y)-x=-(Complex.I • y) := by abel
  rw [he,norm_neg]
  exact complexUnit_norm y

theorem backward_map_sub_free_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a≤b) (ub : EnergyState) (u : CriticalPath (intervalMeasure a b)) :
    ‖backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u -
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)‖ ≤
      max (energyEndpointConstant K C0) (Ch*C0+Cr) *
        ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ := by
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
  let r := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  unfold backwardHartreeDuhamelMap
  change ‖(f-Complex.I • r)-f‖≤_
  exact (norm_decrement_sub_free f r).le.trans
    (intervalAdvancedCriticalPath_norm hDensity hSob h0 hfree hret _)

/-- The radius is selected before the interval and terminal datum. The only
conditional inputs are genuine free-path caps, later discharged by the actual
free tail producer. The nonlinear self-map and contraction are proved here. -/
theorem exists_uniform_backward_terminal_radius (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B delta : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hB : 0<B) (hdelta : 0<delta) :
    ∃ eta : ℝ, 0<eta ∧ eta≤delta ∧ ∀ {a b : ℝ} (hab : a≤b) (ub : EnergyState),
      ‖energyPath _ (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-b) ub))‖≤B/2 →
      (∀ j : Fin 3, ‖criticalGradient _ j (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-b) ub))‖≤eta/2) →
      ∃ u : CriticalPath (intervalMeasure a b),
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u=u ∧
        energyPath _ u ⟨b,hab,le_rfl⟩=ub ∧
        ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤eta ∧
        ‖u-freeCriticalPath hDensity hSob hfree a b
          (freeEnergyState hDensity hSob (-b) ub)‖≤eta/2 := by
  let comparisonChoice := exists_actual_backward_source_smallness_and_contraction
    hDensity hSob h0 hfree hret hH hB.le
  let rho : ℝ := Classical.choose comparisonChoice
  have hrho : 0<rho := (Classical.choose_spec comparisonChoice).1
  let singleChoice := criticalPathIntervalSource_cap_single_bound hDensity hSob hH
  let C : ℝ≥0 := Classical.choose singleChoice
  let Q := max (energyEndpointConstant K C0) (Ch*C0+Cr)
  have hQ : 0≤Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  let D := Q*(C:ℝ)*B^(2*alpha)*(normComparisonConstant K)^5
  have hL : 0<normComparisonConstant K := normComparisonConstant_pos hSob
  have hD : 0≤D := by dsimp [D]; positivity
  let radiusChoice := exists_small_fifth_power_radius_below D B (min rho delta)
    hD hB (lt_min hrho hdelta)
  let eta : ℝ := Classical.choose radiusChoice
  have heta : 0<eta := (Classical.choose_spec radiusChoice).1
  have hetamin : eta ≤ min rho delta := (Classical.choose_spec radiusChoice).2.1
  have hfifth : D*eta^5≤eta/2 := (Classical.choose_spec radiusChoice).2.2.2.2.2.1
  have hfifthB : D*eta^5≤B/16 := (Classical.choose_spec radiusChoice).2.2.2.2.2.2
  have hetarho : eta≤rho := hetamin.trans (min_le_left _ _)
  refine ⟨eta,heta,hetamin.trans (min_le_right _ _),?_⟩
  intro a b hab ub hfreeE hfreeW
  let μ := intervalMeasure a b
  let t0 : Set.Icc a b := ⟨b,hab,le_rfl⟩
  let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
  let Φ := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub
  let S := admissiblePaths μ t0 ub B eta
  have hf : f∈S := by
    apply admissiblePaths_mem_of_coordinates μ heta.le
    · exact backwardFreeCriticalPath_terminal hDensity hSob hfree hab ub
    · exact hfreeE.trans (by linarith)
    · intro j; exact (hfreeW j).trans (by linarith)
  have hsource (u : CriticalPath μ) (hu : u∈S) :
      Q*‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖≤D*eta^5 := by
    have hg : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖≤
        (C:ℝ)*B^(2*alpha)*(normComparisonConstant K)^5*eta^5 := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      exact (Classical.choose_spec singleChoice) hab u B eta hB.le heta.le hu.2.1 hu.2.2
    exact (mul_le_mul_of_nonneg_left hg hQ).trans_eq (by dsimp [D]; ring)
  have hself : Set.MapsTo Φ S S := by
    intro u hu
    apply admissiblePaths_mem_of_coordinates μ heta.le
    · exact backwardHartreeDuhamelMap_terminal hDensity hSob h0 hfree hret hH hab ub u
    · have he : energyEndpointConstant K C0*
          ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖≤D*eta^5 :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)).trans (hsource u hu)
      have hb := (backwardHartreeDuhamelMap_energy_norm hDensity hSob h0 hfree hret hH
        hab ub u).trans (add_le_add hfreeE (he.trans hfifthB))
      linarith
    · intro j
      have hg : (Ch*C0+Cr)*‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j‖≤
          D*eta^5 :=
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j)
          (add_nonneg (mul_nonneg hfree.1 h0.1) hret.1)).trans
          ((mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)).trans (hsource u hu))
      exact (backwardHartreeDuhamelMap_gradient_norm hDensity hSob h0 hfree hret hH
        hab ub u j).trans ((add_le_add (hfreeW j) (hg.trans hfifth)).trans_eq (by ring))
  have hc : ∀ u∈S, ∀ v∈S, ‖Φ u-Φ v‖≤(1/2:ℝ)*‖u-v‖ := by
    intro u hu v hv
    exact ((Classical.choose_spec comparisonChoice).2.2 hab ub u v hu.2.1 hv.2.1
      (hu.2.2.trans hetarho) (hv.2.2.trans hetarho)).2
  let fixedChoice := exists_unique_fixedPoint_of_bounds μ t0 ub B eta Φ ⟨f,hf⟩ hself hc
  let u : CriticalPath μ := Classical.choose fixedChoice
  have hu : u∈S := (Classical.choose_spec fixedChoice).1
  have hfix : Φ u=u := (Classical.choose_spec fixedChoice).2.1
  refine ⟨u,hfix,hu.1,hu.2.1,hu.2.2,?_⟩
  have herr := backward_map_sub_free_norm hDensity hSob h0 hfree hret hH hab ub u
  change ‖Φ u-f‖≤Q*‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ at herr
  rw [hfix] at herr
  exact herr.trans ((hsource u hu).trans hfifth)

end HartreeF.WaveTerminal
