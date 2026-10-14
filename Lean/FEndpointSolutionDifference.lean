import FActualHartreeDataDifference
import FEndpointProjectedGradient

/-! The missing endpoint difference estimate. All source terms below are the
literal compatible Hartree source for the two paths. The only endpoint analytic
interfaces are the previously accepted numerical KT(5)/(7) specializations. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.EndpointOutput
open MeasureTheory Filter TimeHolder EnergySpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathSpace SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
open FreeDataDependence
open scoped ENNReal NNReal
attribute [local irreducible] criticalPathIntervalSource intervalRetardedCriticalPath freeCriticalPath
  hartreeDuhamelMap CriticalJointSources.jointFields
  freeCriticalPath_endpointWitness intervalRetardedCriticalPath_endpointWitness

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha c a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 v0 : EnergyState)
  (u v : CriticalPath (intervalMeasure a b))
include hDensity hSob h0 hfree hret hefree heret hH hab u0 v0 u v

/-- This is a constructed endpoint witness for the literal two-data map
difference, with the actual forcing-difference source. Agreement is AE in time
and then AE in space, as in the accepted endpoint module. -/
def hartreeDuhamelMap_two_data_endpointWitness :
    EndpointGradientWitness (intervalMeasure a b)
      (fun t => energyPath (intervalMeasure a b) (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v) t) := by
  let Wfree := freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
    (freeEnergyState hDensity hSob (-a) (u0-v0))
  let Wret := intervalRetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret
    (criticalPathIntervalSource hDensity hSob hH hab u v)
  refine ⟨fun j => Wfree.field j + Complex.I • Wret.field j, ?_⟩
  intro j
  filter_upwards [(Wfree.add (Wret.smul Complex.I)).agrees j] with t ht
  have hp := actual_hartreeDuhamelMap_two_data_sub hDensity hSob h0 hfree hret hH hab u0 v0 u v
  have he : energyPath (intervalMeasure a b)
      (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v) t =
      energyPath (intervalMeasure a b) (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-a) (u0-v0))) t +
      Complex.I • energyPath (intervalMeasure a b)
        (intervalRetardedCriticalPath hDensity hSob h0 hret
          (criticalPathIntervalSource hDensity hSob hH hab u v)) t := by
    simpa only [map_add, map_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply] using
      congrArg (fun p : CriticalPath (intervalMeasure a b) =>
        energyPath (intervalMeasure a b) p t) hp
  exact ht.trans (Eventually.of_forall fun x =>
    congrArg (fun w : EnergyState => energyGradient j w x) he.symm)

/-- Coordinatewise endpoint norm of the constructed difference witness. -/
theorem hartreeDuhamelMap_two_data_endpoint_enorm_bound (j : Fin 3) :
    ‖(hartreeDuhamelMap_two_data_endpointWitness hDensity hSob h0 hfree hret
      hefree heret hH hab u0 v0 u v).field j‖ₑ ≤
      ENNReal.ofReal (Che * ‖energyGradient j (u0-v0)‖) +
      ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖) := by
  change ‖(freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
      (freeEnergyState hDensity hSob (-a) (u0-v0))).field j + Complex.I •
        (intervalRetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret
          (criticalPathIntervalSource hDensity hSob hH hab u v)).field j‖ₑ ≤ _
  refine (endpoint_enorm_add_I_le (μ := intervalMeasure a b) _ _).trans (add_le_add ?_ ?_)
  · simpa only [freeEnergyState_gradient, FreeFlow.freeL2_norm] using
      freeCriticalPath_endpoint_enorm_bound hDensity hSob hfree hefree a b
        (freeEnergyState hDensity hSob (-a) (u0-v0)) j
  · exact intervalRetardedCriticalPath_endpoint_enorm_bound hDensity hSob h0 hret heret
      (criticalPathIntervalSource hDensity hSob hH hab u v) j

/-- The same quantitative bound is on the actual gradient of the map difference. -/
theorem hartreeDuhamelMap_two_data_endpoint_bound (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath (intervalMeasure a b)
        (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u -
          hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v) t)) ≤
      ENNReal.ofReal (Che * ‖energyGradient j (u0-v0)‖) +
      ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖) := by
  rw [(hartreeDuhamelMap_two_data_endpointWitness hDensity hSob h0 hfree hret
    hefree heret hH hab u0 v0 u v).mixedNorm_eq]
  exact hartreeDuhamelMap_two_data_endpoint_enorm_bound hDensity hSob h0 hfree hret
    hefree heret hH hab u0 v0 u v j

variable (hu : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u)
  (hv : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab v0 v = v)
include hu hv

/-- Two literal fixed points have a constructed endpoint witness on their
literal path difference, even when the initial data differ. -/
def fixedPoint_difference_endpointWitness :
    EndpointGradientWitness (intervalMeasure a b) (energyPath (intervalMeasure a b) (u-v)) := by
  simpa only [hu, hv] using hartreeDuhamelMap_two_data_endpointWitness
    hDensity hSob h0 hfree hret hefree heret hH hab u0 v0 u v

/-- All three actual complex spatial derivatives of the solution difference
obey the endpoint (2,6) estimate. No endpoint output bound is assumed. -/
theorem fixedPoint_difference_endpoint_bound (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath (intervalMeasure a b) (u-v) t)) ≤
      ENNReal.ofReal (Che * ‖energyGradient j (u0-v0)‖) +
      ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖) := by
  simpa only [hu, hv] using hartreeDuhamelMap_two_data_endpoint_bound
    hDensity hSob h0 hfree hret hefree heret hH hab u0 v0 u v j

/-- A per-coordinate B is an input source bound, to be supplied by the native
Hartree source-cap producer. It is not an assumed solution/output estimate. -/
theorem fixedPoint_difference_endpoint_bound_of_source_bound {B : ℝ}
    (hB : ∀ j : Fin 3,
      ‖(criticalPathIntervalSource hDensity hSob hH hab u v).gradient j‖ ≤ B)
    (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath (intervalMeasure a b) (u-v) t)) ≤
      ENNReal.ofReal (Che * ‖u0-v0‖) + ENNReal.ofReal (Cre * B) := by
  exact (fixedPoint_difference_endpoint_bound hDensity hSob h0 hfree hret hefree heret
    hH hab u0 v0 u v hu hv j).trans (add_le_add
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (energyState_gradient_norm_le (u0-v0) j) hefree.1))
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB j) heret.1)))

end HartreeF.EndpointOutput
