import FActualIntervalSourceBounds
import FActualHartreeDuhamelDifference
import FActualFreePathDifference
import FMildHartreeDefinition

/-! A uniform small-S graph bound on the very same literal mild path.
The accepted actual source producer is specialized against zero. Its only
small-W hypothesis is then a theorem about zero; the input path needs only
an energy bound and small actual L10_t L10_x size. No conservation law or
continuation conclusion is asserted here. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal NNReal Topology
namespace HartreeF.SmallSGraphBound
open EnergySpace CriticalPathSpace CriticalSourceBounds ActualDuhamelPath
open IntervalTimeTransport SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness FreeDataDependence
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  criticalPathIntervalSource hartreeDuhamelMap freeCriticalPath energyPath criticalGradient

/-- This is the norm of the actual constructed source, with no source witness
or source estimate as an input. The threshold precedes the interval and path. -/
theorem exists_small_s_actual_source_norm (hDensity : OrdinaryH1Density)
    {K alpha c B epsilon : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
    (u : CriticalPath (intervalMeasure a b)),
    pathEnergySize (intervalMeasure a b) u ≤ ENNReal.ofReal B →
    pathValueSize (intervalMeasure a b) u ≤ ENNReal.ofReal eta →
    ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤ epsilon * ‖u‖ := by
  let choice := criticalPathIntervalSource_uniform_smallness hDensity hSob hH hB hepsilon
  let eta : ℝ := Classical.choose choice
  have heta : 0 < eta := (Classical.choose_spec choice).1
  have heta1 : eta ≤ 1 := (Classical.choose_spec choice).2.1
  refine ⟨eta, heta, heta1, ?_⟩
  intro a b hab u hE hS
  have hEzero : pathEnergySize (intervalMeasure a b) u +
      pathEnergySize (intervalMeasure a b) 0 ≤ ENNReal.ofReal B := by
    simpa only [pathEnergySize_zero, add_zero] using hE
  have hSzero : pathValueSize (intervalMeasure a b) u +
      pathValueSize (intervalMeasure a b) 0 ≤ ENNReal.ofReal eta := by
    simpa only [pathValueSize_zero (intervalMeasure a b) hDensity hSob, add_zero] using hS
  have hWzero : pathGradientSize (intervalMeasure a b) 0 ≤ ENNReal.ofReal eta := by
    rw [pathGradientSize_zero]
    exact bot_le
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hepsilon.le (norm_nonneg u))).mpr
  intro j
  have hsource := (Classical.choose_spec choice).2.2 hab u 0 hEzero hSzero hWzero j
  have hn : ‖u - 0‖ = ‖u‖ := congrArg (fun v : CriticalPath (intervalMeasure a b) => ‖v‖)
    (_root_.sub_zero u)
  exact hsource.trans_eq (congrArg (fun x : ℝ => epsilon * x) hn)

/-- Small actual S and a prescribed native energy-size bound control the
same finite-interval literal mild path in its canonical E+W graph norm.
The free constant is exactly the accepted shifted Fourier free-path bound;
the retarded constant is exactly max(energyEndpointConstant K C0, Cr).
All quantities absorbed are finite real norms. -/
theorem exists_small_s_mild_graph_norm_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
    (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b)),
    IsMildHartreePath hab alpha c u0 u →
    pathEnergySize (intervalMeasure a b) u ≤ ENNReal.ofReal B →
    pathValueSize (intervalMeasure a b) u ≤ ENNReal.ofReal eta →
    ‖u‖ ≤ 2 * max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖u0‖ := by
  let Q := max (energyEndpointConstant K C0) Cr
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  let epsilon := 1 / (2 * (Q + 1))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  let choice := exists_small_s_actual_source_norm hDensity hSob hH hB hepsilon
  let eta : ℝ := Classical.choose choice
  have heta : 0 < eta := (Classical.choose_spec choice).1
  have heta1 : eta ≤ 1 := (Classical.choose_spec choice).2.1
  refine ⟨eta, heta, heta1, ?_⟩
  intro a b hab u0 u hmild hE hS
  have hfixed := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret
    hH hab u0 u).mp hmild
  have hmap := hartreeDuhamelMap_norm hDensity hSob h0 hfree hret hH hab u0 u
  rw [hfixed] at hmap
  have hfreeBound := actual_shiftedFreeCriticalPath_norm_le hDensity hSob hfree a b u0
  have hsourceBound := (Classical.choose_spec choice).2.2 hab u hE hS
  have hcoeff : Q * epsilon ≤ (1/2 : ℝ) := by
    dsimp [epsilon]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*(Q+1))).mpr
    linarith
  have hretarded : Q * ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤
      (1/2 : ℝ) * ‖u‖ :=
    (mul_le_mul_of_nonneg_left hsourceBound hQ).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff (norm_nonneg u))
  have habsorb := hmap.trans (add_le_add hfreeBound hretarded)
  linarith

/-- The natural energy-coordinate hypothesis explicitly implies the native
L-infinity-time L6-size bound used above. No energy conservation premise is
introduced. The threshold is uniform in the interval, initial datum and path. -/
theorem exists_small_s_energy_coordinate_graph_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
    (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b)),
    IsMildHartreePath hab alpha c u0 u →
    ‖energyPath (intervalMeasure a b) u‖ ≤ B →
    pathValueSize (intervalMeasure a b) u ≤ ENNReal.ofReal eta →
    ‖u‖ ≤ 2 * max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖u0‖ := by
  let choice := exists_small_s_mild_graph_norm_bound hDensity hSob h0 hfree hret hH hB
  let eta : ℝ := Classical.choose choice
  have heta : 0 < eta := (Classical.choose_spec choice).1
  have heta1 : eta ≤ 1 := (Classical.choose_spec choice).2.1
  refine ⟨eta, heta, heta1, ?_⟩
  intro a b hab u0 u hmild hE hS
  have hnative : pathEnergySize (intervalMeasure a b) u ≤ ENNReal.ofReal B :=
    (joint_value_energy_projection_bound (intervalMeasure a b) u).trans
      (ENNReal.ofReal_le_ofReal hE)
  exact (Classical.choose_spec choice).2.2 hab u0 u hmild hnative hS

set_option pp.universes true
#check @HartreeF.SmallSGraphBound.exists_small_s_actual_source_norm
#print axioms HartreeF.SmallSGraphBound.exists_small_s_actual_source_norm
#check @HartreeF.SmallSGraphBound.exists_small_s_mild_graph_norm_bound
#print axioms HartreeF.SmallSGraphBound.exists_small_s_mild_graph_norm_bound
#check @HartreeF.SmallSGraphBound.exists_small_s_energy_coordinate_graph_bound
#print axioms HartreeF.SmallSGraphBound.exists_small_s_energy_coordinate_graph_bound
#check @HartreeF.CriticalPathSpace.criticalPath_norm
#check @HartreeF.CriticalSourceBounds.pathValueSize
#check @HartreeF.CriticalUniqueness.IsMildHartreePath
end HartreeF.SmallSGraphBound
