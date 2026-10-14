import FUniformActualForwardCap
import FActualFreePathDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.WaveInitial
open EnergySpace CriticalPathSpace CriticalPathBall CriticalSourceBounds
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain UniformLocalData
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource energyPath

/-- The forward radius is selected before the interval and initial datum.
The existing actual forward cap producer supplies the fixed point; a smaller
radius makes its literal nonlinear graph error at most eta/2. -/
theorem exists_uniform_forward_initial_radius (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B delta : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hB : 0<B) (hdelta : 0<delta) :
    ∃ eta : ℝ, 0<eta ∧ eta≤delta ∧ ∀ {a b : ℝ} (hab : a≤b) (ua : EnergyState),
      ‖energyPath _ (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) ua))‖≤B/2 →
      (∀ j : Fin 3, ‖criticalGradient _ j (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) ua))‖≤eta/2) →
      ∃ u : CriticalPath (intervalMeasure a b),
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ua u=u ∧
        energyPath _ u ⟨a,le_rfl,hab⟩=ua ∧
        ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤eta ∧
        ‖u-freeCriticalPath hDensity hSob hfree a b
          (freeEnergyState hDensity hSob (-a) ua)‖≤eta/2 := by
  let singleChoice := criticalPathIntervalSource_cap_single_bound hDensity hSob hH
  let C : ℝ≥0 := Classical.choose singleChoice
  let Q := max (energyEndpointConstant K C0) Cr
  have hQ : 0≤Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  let D := Q*(C:ℝ)*B^(2*alpha)*(normComparisonConstant K)^5
  have hL : 0<normComparisonConstant K := normComparisonConstant_pos hSob
  have hD : 0≤D := by dsimp [D]; positivity
  let radiusChoice := exists_small_fifth_power_radius_below D B delta hD hB hdelta
  let rho : ℝ := Classical.choose radiusChoice
  have hrho : 0<rho := (Classical.choose_spec radiusChoice).1
  have hrhod : rho≤delta := (Classical.choose_spec radiusChoice).2.1
  have hrho4 : D*rho^4≤1/2 := (Classical.choose_spec radiusChoice).2.2.2.2.1
  let capChoice := exists_uniform_actual_forward_cap hDensity hSob h0 hfree hret hH hB hrho
  let eta : ℝ := Classical.choose capChoice
  have heta : 0<eta := (Classical.choose_spec capChoice).1
  have hetarho : eta≤rho := (Classical.choose_spec capChoice).2.1
  have heta4 : D*eta^4≤1/2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ heta.le hetarho 4) hD).trans hrho4
  have heta5 : D*eta^5≤eta/2 := by
    have h := mul_le_mul_of_nonneg_right heta4 heta.le
    nlinarith [h]
  refine ⟨eta,heta,hetarho.trans hrhod,?_⟩
  intro a b hab ua hfreeE hfreeW
  let solved := (Classical.choose_spec capChoice).2.2 hab ua hfreeE hfreeW
  let u : CriticalPath (intervalMeasure a b) := Classical.choose solved
  have hfix := (Classical.choose_spec solved).1
  have hinitial := (Classical.choose_spec solved).2.1
  have huE := (Classical.choose_spec solved).2.2.1
  have huW : ‖fun j => criticalGradient _ j u‖≤eta := (Classical.choose_spec solved).2.2.2
  have hg : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖≤
      (C:ℝ)*B^(2*alpha)*(normComparisonConstant K)^5*eta^5 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    exact (Classical.choose_spec singleChoice) hab u B eta hB.le heta.le huE huW
  have hsource : Q*‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖≤D*eta^5 :=
    (mul_le_mul_of_nonneg_left hg hQ).trans_eq (by dsimp [D]; ring)
  refine ⟨u,hfix,hinitial,huE,huW,?_⟩
  have herr := hartreeDuhamelMap_sub_free_norm hDensity hSob h0 hfree hret hH hab ua u
  rw [hfix] at herr
  exact herr.trans (hsource.trans heta5)

end HartreeF.WaveInitial
