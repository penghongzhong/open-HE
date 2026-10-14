import FScalarFiniteEndpointEstimate
import FActualUniformChargeDerivative
import FFiniteEndpointMassRecovery

/-!
The first finite-interval estimate in the actual finite-endpoint consumer.
The original value has no L2 input. Vanishing of each original localized
charge at the finite endpoint is an explicit intermediate input, to be
produced by the separately implemented compact-profile argument.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff
namespace HartreeF.ActualFiniteEndpointCharge
open EnergySpace LocalChargeBridge LocalDualSource LocalChargeRigidity
open ForcingDomain SobolevStretch StationarySelfTest CompactPDEDualBridge
open CutoffApproximation FiniteEndpointCalculus FiniteEndpointMassRecovery
attribute [local instance] energyRealSpace energyDualComplexNorm energyDualRealNorm
  energyDualComplexSpace energyDualRealSpace

/-- The actual uniform local flux constant times the squared gradient cap. -/
def finiteChargeSlope (K B : ℝ) : ℝ := uniformChargeFluxConstant K * B ^ 2

theorem finiteChargeSlope_nonneg {K : ℝ} (hSob : OrdinarySobolev K) (B : ℝ) :
    0 ≤ finiteChargeSlope K B :=
  mul_nonneg (uniformChargeFluxConstant_nonneg hSob) (sq_nonneg B)

/-- First actual finite-segment estimate, after sending its upper endpoint
to T. All derivatives are produced from the original tensor PDE. -/
theorem original_charge_le_finite_endpoint
    (hD : OrdinaryH1Density) {K α c B T : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hord : OrdConnected S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    (hT : T ∈ closure S) (hbefore : ∀ t ∈ S, t < T)
    (hcap : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    (hzero : ∀ n : ℕ, Tendsto
      (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (u t))) (𝓝[S] T) (𝓝 0))
    (n : ℕ) {a : ℝ} (ha : a ∈ S) :
    spatialCharge ((n : ℝ) + 1) (energyValue (u a)) ≤
      finiteChargeSlope K B * (T - a) := by
  apply (le_abs_self _).trans
  apply abs_le_endpoint_of_hasDerivAt_bound hord hT ha (hbefore a ha)
    (fun t ht => original_spatialCharge_derivative_flux hD hSob
      (by positivity : 0 < (n : ℝ) + 1) hH hS hu hp ht) _ (hzero n)
  intro t ht _hat
  exact (originalFlux_uniform_nat_bound hSob n (u t)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (pureGradientNorm_nonneg (u t)) (hcap t ht) 2)
      (uniformChargeFluxConstant_nonneg hSob))

/-- Fatou recovers L2 for the SAME original representative and a quantitative
mass bound at each actual time. No L2-valued time path is constructed. -/
theorem original_memLp_two_and_mass_bound
    (hD : OrdinaryH1Density) {K α c B T : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hord : OrdConnected S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    (hT : T ∈ closure S) (hbefore : ∀ t ∈ S, t < T)
    (hcap : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    (hzero : ∀ n : ℕ, Tendsto
      (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (u t))) (𝓝[S] T) (𝓝 0))
    {a : ℝ} (ha : a ∈ S) :
    MemLp (energyValue (u a) : V → ℂ) 2 volume ∧
      (∫ x : V, ‖energyValue (u a) x‖ ^ 2) ≤ finiteChargeSlope K B * (T - a) := by
  apply memLp_two_of_localized_mass_bound
    (χ := fun n => chargeCutoff ((n : ℝ) + 1))
    (Lp.aestronglyMeasurable (energyValue (u a)))
    (mul_nonneg (finiteChargeSlope_nonneg hSob B) (sub_nonneg.mpr (hbefore a ha).le))
  · intro n
    exact Eventually.of_forall (chargeCutoff_nonneg ((n : ℝ) + 1))
  · intro n
    exact (original_spatialCharge_form (by positivity : 0 < (n : ℝ) + 1) (u a)).1
  · exact Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [cutoff_eventually_one x] with n hn
      simpa only [chargeCutoff_nat_succ_eq_cutoff] using hn.symm)
  · intro n
    exact original_charge_le_finite_endpoint hD hSob hH hS hord hu hp hT hbefore
      hcap hzero n ha

end HartreeF.ActualFiniteEndpointCharge
