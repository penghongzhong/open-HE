import FSmallSGraphBound
import FActualL1ForcingDefect

/-! The preliminary small-S bound for the actual approximate path with its
original L1 scalar error. The nonlinear source is produced and absorbed;
neither small W nor a global W bound is an input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcedSmallS
open EnergySpace CriticalPathSpace CriticalSourceBounds ActualDuhamelPath
open IntervalTimeTransport SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness FreeDataDependence SmallSGraphBound ActualPerturbation
attribute [local instance] ActualPerturbation.canonicalEnergyNormedSpace
  ActualPerturbation.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  criticalPathIntervalSource hartreeDuhamelMap freeCriticalPath energyPath criticalGradient

/-- A true forced mild identity yields the path norm inequality with the
actual Hartree source and the actual L1 retarded error. -/
theorem actual_forced_path_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (g : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (E : CompatibleL1IntervalSource a b)
    (hforced : q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
      Complex.I • E.retardedCriticalPath hDensity hSob h0 hret) :
    ‖q‖ ≤ max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖g‖ +
      max (energyEndpointConstant K C0) Cr *
        ‖(criticalPathIntervalSource hDensity hSob hH hab q 0).gradient‖ +
      max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ := by
  let Φ := hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q
  let R := E.retardedCriticalPath hDensity hSob h0 hret
  have hn : ‖q‖ ≤ ‖Φ‖ + ‖Complex.I • R‖ :=
    (congrArg norm hforced).trans_le (norm_sub_le Φ (Complex.I • R))
  have hPhi := (hartreeDuhamelMap_norm hDensity hSob h0 hfree hret hH hab g q).trans
    (add_le_add (actual_shiftedFreeCriticalPath_norm_le hDensity hSob hfree a b g) (le_refl _))
  have hR : ‖Complex.I • R‖ ≤ max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ :=
    (complexUnit_norm R).trans_le (E.retardedCriticalPath_norm_le hDensity hSob h0 hret)
  exact hn.trans (add_le_add hPhi hR)

/-- The radius precedes the interval, path and error. Small actual scalar S
plus an energy-coordinate cap absorbs the produced nonlinear source. -/
theorem exists_small_s_forced_graph_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (g : EnergyState) (q : CriticalPath (intervalMeasure a b))
      (E : CompatibleL1IntervalSource a b),
      q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
        Complex.I • E.retardedCriticalPath hDensity hSob h0 hret →
      ‖energyPath (intervalMeasure a b) q‖ ≤ B →
      pathValueSize (intervalMeasure a b) q ≤ ENNReal.ofReal eta →
      ‖q‖ ≤ 2 * (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖g‖ +
        max (energyEndpointConstant K C0) Cr * ‖E.gradient‖) := by
  let Q := max (energyEndpointConstant K C0) Cr
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  let epsilon := 1/(2*(Q+1))
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  let choice := exists_small_s_actual_source_norm hDensity hSob hH hB hepsilon
  let eta : ℝ := Classical.choose choice
  refine ⟨eta, (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.1, ?_⟩
  intro a b hab g q E hforced hE hS
  have hsize : pathEnergySize (intervalMeasure a b) q ≤ ENNReal.ofReal B :=
    (joint_value_energy_projection_bound (intervalMeasure a b) q).trans
      (ENNReal.ofReal_le_ofReal hE)
  have hsource := (Classical.choose_spec choice).2.2 hab q hsize hS
  have hcoeff : Q*epsilon ≤ (1/2 : ℝ) := by
    dsimp [epsilon]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2*(Q+1))).mpr
    linarith
  have hretarded : Q*‖(criticalPathIntervalSource hDensity hSob hH hab q 0).gradient‖ ≤
      (1/2 : ℝ)*‖q‖ :=
    (mul_le_mul_of_nonneg_left hsource hQ).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoeff (norm_nonneg q))
  have hnorm := actual_forced_path_norm hDensity hSob h0 hfree hret hH hab g q E hforced
  change ‖q‖ ≤ 2 * (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖g‖ + Q*‖E.gradient‖)
  change ‖q‖ ≤ max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖g‖ +
    Q*‖(criticalPathIntervalSource hDensity hSob hH hab q 0).gradient‖ + Q*‖E.gradient‖ at hnorm
  linarith

#print axioms actual_forced_path_norm
#print axioms exists_small_s_forced_graph_bound
end HartreeF.ForcedSmallS
