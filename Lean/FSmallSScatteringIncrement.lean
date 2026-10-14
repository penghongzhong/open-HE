import FActualScatteringIncrement

/-! Actual small-S control of the free-back-propagated endpoint increment.
The threshold is chosen before the interval, datum, and literal mild path.
The only trajectory size input is an energy-state norm cap. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualScattering
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness CriticalSourceBounds SmallSGraphBound MaximalTrajectory
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalPathIntervalSource hartreeDuhamelMap freeCriticalPath freeEnergyState

/-- Numerical normalization isolated from the actual path types. -/
theorem normalized_increment_coefficient {A Q M epsilon : ℝ}
    (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (he : 0 ≤ epsilon) :
    A * (Q * ((epsilon / (A*Q*M+1)) * M)) ≤ epsilon := by
  have hD : 0 ≤ A*Q*M := mul_nonneg (mul_nonneg hA hQ) hM
  calc
    _ = (A*Q*M)*epsilon/(A*Q*M+1) := by ring
    _ ≤ epsilon := (div_le_iff₀ (by positivity : 0 < A*Q*M+1)).mpr (by nlinarith only [he])

/-- Finite actual S can later supply this interval-uniform threshold. The
conclusion is an arbitrarily small actual free-back endpoint difference,
without any smallness assumption on W or any conservation premise. -/
theorem exists_small_s_backprop_increment (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B epsilon : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hB : 0 ≤ B) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b)),
      IsMildHartreePath hab alpha kernel u0 u →
      ‖u0‖ ≤ B → ‖energyPath (intervalMeasure a b) u‖ ≤ B →
      pathValueSize (intervalMeasure a b) u ≤ ENNReal.ofReal eta →
      ‖freeEnergyState hDensity hSob (-b)
          (energyPath (intervalMeasure a b) u ⟨b, hab, le_rfl⟩) -
        freeEnergyState hDensity hSob (-a) u0‖ ≤ epsilon := by
  let kf : ℝ := max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3
  let cf : ℝ := max kf Ch
  let Q : ℝ := max (energyEndpointConstant K C0) Cr
  let M : ℝ := 2 * cf * B
  let D : ℝ := kf * Q * M
  have hkf : 0 ≤ kf := by dsimp [kf]; positivity
  have hcf : 0 ≤ cf := hkf.trans (le_max_left _ _)
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let epsilon' : ℝ := epsilon / (D+1)
  have hepsilon' : 0 < epsilon' := by dsimp [epsilon']; positivity
  let choiceS := exists_small_s_actual_source_norm hDensity hSob hH hB hepsilon'
  let etaS : ℝ := Classical.choose choiceS
  have hetaS := (Classical.choose_spec choiceS).1
  have hetaS1 := (Classical.choose_spec choiceS).2.1
  let choiceG := exists_small_s_energy_coordinate_graph_bound hDensity hSob h0 hfree hret hH hB
  let etaG : ℝ := Classical.choose choiceG
  have hetaG := (Classical.choose_spec choiceG).1
  refine ⟨min etaS etaG, lt_min hetaS hetaG, (min_le_left _ _).trans hetaS1, ?_⟩
  intro a b hab u0 u hu hu0 hE hS
  have hSS : pathValueSize (intervalMeasure a b) u ≤ ENNReal.ofReal etaS :=
    hS.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hSG : pathValueSize (intervalMeasure a b) u ≤ ENNReal.ofReal etaG :=
    hS.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  have hnative : pathEnergySize (intervalMeasure a b) u ≤ ENNReal.ofReal B :=
    (joint_value_energy_projection_bound (intervalMeasure a b) u).trans
      (ENNReal.ofReal_le_ofReal hE)
  have hnorm : ‖u‖ ≤ M := ((Classical.choose_spec choiceG).2.2 hab u0 u hu hE hSG).trans
    (mul_le_mul_of_nonneg_left hu0 (mul_nonneg (by norm_num) hcf))
  have hsourceNorm : ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤
      epsilon' * M := ((Classical.choose_spec choiceS).2.2 hab u hnative hSS).trans
        (mul_le_mul_of_nonneg_left hnorm hepsilon'.le)
  calc
    _ ≤ kf * (Q * ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖) :=
      mild_backprop_increment_norm hDensity hSob h0 hfree hret hH hab u0 u hu
    _ ≤ kf * (Q * (epsilon' * M)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsourceNorm hQ) hkf
    _ ≤ epsilon := normalized_increment_coefficient hkf hQ hM hepsilon.le

set_option pp.universes true
#check @normalized_increment_coefficient
#print axioms normalized_increment_coefficient
#check @exists_small_s_backprop_increment
#print axioms exists_small_s_backprop_increment
end HartreeF.ActualScattering
