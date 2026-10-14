import FActualUniformChargeFlux
import FActualCompactPDEToChargeDerivative

/-! The pre-L2 spatial estimate consumed by the existing actual PDE bridge. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Set
open scoped Topology ContDiff
namespace HartreeF.CompactPDEDualBridge
open EnergySpace LocalChargeBridge LocalDualSource LocalChargeRigidity
open ForcingDomain SobolevStretch StationarySelfTest
attribute [local instance] energyRealSpace energyDualComplexNorm energyDualRealNorm
  energyDualComplexSpace energyDualRealSpace

/-- Every original cutoff charge has a radius-uniform derivative estimate at
EACH point of the exact open PDE domain, before any global L2 conclusion. -/
theorem original_spatialCharge_deriv_uniform_nat_bound
    (hD : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) (n : ℕ) {t : ℝ} (ht : t ∈ S) :
    |deriv (fun s => spatialCharge ((n : ℝ) + 1) (energyValue (u s))) t| ≤
      uniformChargeFluxConstant K * pureGradientNorm (u t) ^ 2 := by
  rw [(original_spatialCharge_derivative_flux hD hSob
    (by positivity : 0 < (n : ℝ) + 1) hH hS hu hp ht).deriv]
  exact originalFlux_uniform_nat_bound hSob n (u t)

/-- Uniform bound with all radius/time quantifiers exposed for exhaustion. -/
theorem exists_original_spatialCharge_deriv_uniform_nat_bound
    (hD : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (t : ℝ), t ∈ S →
      |deriv (fun s => spatialCharge ((n : ℝ) + 1) (energyValue (u s))) t| ≤
        C * pureGradientNorm (u t) ^ 2 := by
  refine ⟨uniformChargeFluxConstant K, uniformChargeFluxConstant_nonneg hSob, ?_⟩
  intro n t ht
  exact original_spatialCharge_deriv_uniform_nat_bound hD hSob hH hS hu hp n ht

#print axioms original_spatialCharge_deriv_uniform_nat_bound
#print axioms exists_original_spatialCharge_deriv_uniform_nat_bound
end HartreeF.CompactPDEDualBridge
