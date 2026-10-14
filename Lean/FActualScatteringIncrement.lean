import FSmallSTailContinuation

/-! Actual finite-interval scattering increments. The source is the already
constructed literal Hartree source of the same mild path; no source witness
or Duhamel estimate is assumed. -/
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

/-- A literal mild path differs from its actual free path by the norm of its
actual gradient source, with the accepted retarded constant. -/
theorem mild_path_sub_free_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hu : IsMildHartreePath hab alpha kernel u0 u) :
    ‖u - freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-a) u0)‖ ≤
      max (energyEndpointConstant K C0) Cr *
        ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ := by
  have hf := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret
    hH hab u0 u).mp hu
  have h := hartreeDuhamelMap_sub_free_norm hDensity hSob h0 hfree hret hH hab u0 u
  rw [hf] at h
  exact h

/-- Back-propagating the actual endpoint difference only uses the uniform
bound of the constructed full energy free group. -/
theorem mild_backprop_increment_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hu : IsMildHartreePath hab alpha kernel u0 u) :
    ‖freeEnergyState hDensity hSob (-b)
        (energyPath (intervalMeasure a b) u ⟨b, hab, le_rfl⟩) -
      freeEnergyState hDensity hSob (-a) u0‖ ≤
      (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) *
        (max (energyEndpointConstant K C0) Cr *
          ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖) := by
  let f := freeCriticalPath hDensity hSob hfree a b
    (freeEnergyState hDensity hSob (-a) u0)
  let t : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have hb : ‖energyPath (intervalMeasure a b) (u-f) t‖ ≤
      max (energyEndpointConstant K C0) Cr *
        ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ :=
    (energyPath_value_norm_le (intervalMeasure a b) (u-f) t).trans
      (mild_path_sub_free_norm hDensity hSob h0 hfree hret hH hab u0 u hu)
  have hidentity : freeEnergyState hDensity hSob (-b)
      (energyPath (intervalMeasure a b) (u-f) t) =
      freeEnergyState hDensity hSob (-b) (energyPath (intervalMeasure a b) u t) -
        freeEnergyState hDensity hSob (-a) u0 := by
    have hf : energyPath (intervalMeasure a b) f t =
        freeEnergyState hDensity hSob b (freeEnergyState hDensity hSob (-a) u0) :=
      freeCriticalPath_energy hDensity hSob hfree a b _ t
    have hp := congrArg (freeEnergyState hDensity hSob (-b))
      (energyPath_sub_apply (intervalMeasure a b) u f t)
    have hl := freeEnergyState_sub hDensity hSob (-b)
      (energyPath (intervalMeasure a b) u t) (energyPath (intervalMeasure a b) f t)
    have hz := (congrArg (freeEnergyState hDensity hSob (-b)) hf).trans
      (freeEnergyState_left_inverse hDensity hSob b (freeEnergyState hDensity hSob (-a) u0))
    exact hp.trans (hl.trans (congrArg (fun z : EnergyState =>
      freeEnergyState hDensity hSob (-b) (energyPath (intervalMeasure a b) u t) - z) hz))
  rw [← hidentity]
  exact (freeEnergyState_norm_bound hDensity hSob (-b) _).trans
    (mul_le_mul_of_nonneg_left hb (by positivity))

/-- The same estimate for a genuine actual trajectory and its chosen compact
mild path, including a zero-width interval. -/
theorem trajectory_backprop_increment_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a c b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hcb : c ≤ b) (hI : Set.Icc c b ⊆ U.domain) :
    ‖freeEnergyState hDensity hSob (-b) (U.state b) -
      freeEnergyState hDensity hSob (-c) (U.state c)‖ ≤
      (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) *
        (max (energyEndpointConstant K C0) Cr *
          ‖(criticalPathIntervalSource hDensity hSob hH hcb (U.path hcb hI) 0).gradient‖) := by
  have h := mild_backprop_increment_norm hDensity hSob h0 hfree hret hH hcb
    (U.state c) (U.path hcb hI) (U.path_mild hcb hI)
  simpa only [U.path_agrees] using h

set_option pp.universes true
#check @mild_path_sub_free_norm
#print axioms mild_path_sub_free_norm
#check @mild_backprop_increment_norm
#print axioms mild_backprop_increment_norm
#check @trajectory_backprop_increment_norm
#print axioms trajectory_backprop_increment_norm
end HartreeF.ActualScattering
