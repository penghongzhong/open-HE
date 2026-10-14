import FActualTensorScalarWeakIdentity
import FDenseTestDualTimeIdentity
import FActualSpatialGreen

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

/-- The actual compact Hartree tensor PDE supplies the norm-dual derivative
of the SAME mixed original physical charge form on exactly the open domain S. -/
theorem physicalChargeForm_hasDerivAt_of_compactPDE
    (hD : OrdinaryH1Density) {K R α c : ℝ} (hSob : OrdinarySobolev K)
    (hR : 0 < R) (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {t : ℝ} (ht : t ∈ S) :
    HasDerivAt (fun s => physicalChargeForm hR (u s)) (physicalPDEDual hR hH (u t)) t := by
  apply DenseDualTime.hasDerivAt_of_dense_weak_tests (schwartzEnergyState_denseRange hD hSob)
    hS ((physicalChargeForm hR).continuous.comp_continuousOn hu)
    ((physicalPDEDual_continuous hR hH).comp_continuousOn hu) _ ht
  intro η hη hc hs φ
  change (∫ t, deriv η t * physicalChargeForm hR (u t) (schwartzEnergyState φ)) =
    -(∫ t, η t * physicalPDEDual hR hH (u t) (schwartzEnergyState φ))
  have he := real_weak_identity_of_tensor hH hu hp hη hc hs
    (compactConjugateTest (chargeCutoff_smooth R) (chargeCutoff_compact hR) φ)
    (compactConjugateTest_compact (chargeCutoff_smooth R) (chargeCutoff_compact hR) φ)
  simpa only [physicalChargeForm_eq_compactConjugateTest hR, physicalPDEDual,
    actualPDEDual_eq_distribution, stateTest, spatialTest] using he

/-- Original actual cutoff charge integral derivative obtained from weak PDE,
not from an assumed mass derivative or flux equation. -/
theorem original_spatialCharge_hasDerivAt_of_compactPDE
    (hD : OrdinaryH1Density) {K R α c : ℝ} (hSob : OrdinarySobolev K)
    (hR : 0 < R) (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {t : ℝ} (ht : t ∈ S) :
    HasDerivAt (fun s => spatialCharge R (energyValue (u s)))
      (2 * physicalPDEDual hR hH (u t) (u t)) t :=
  original_spatialCharge_hasDerivAt hR (hu.continuousAt (hS.mem_nhds ht))
    (physicalChargeForm_hasDerivAt_of_compactPDE hD hSob hR hH hS hu hp ht)

/-- The derivative is the original coordinate-flux integral, after finite real
Hartree cancellation and all spatial/temporal integrability checks. -/
theorem original_spatialCharge_derivative_flux
    (hD : OrdinaryH1Density) {K R α c : ℝ} (hSob : OrdinarySobolev K)
    (hR : 0 < R) (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {t : ℝ} (ht : t ∈ S) :
    HasDerivAt (fun s => spatialCharge R (energyValue (u s)))
      (2 * ∑ j : Fin 3, (∫ x : V, fluxIntegrand (χ := chargeCutoff R) (u t) j x).im) t := by
  have hd := original_spatialCharge_hasDerivAt_of_compactPDE hD hSob hR hH hS hu hp ht
  simpa only [physicalPDEDual, actualPDEDual_diagonal_flux] using hd

end HartreeF.CompactPDEDualBridge
