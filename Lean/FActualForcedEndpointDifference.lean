import FActualL1MildPerturbation
import FL1RetardedEndpointWitness
import FEndpointComplexVectorDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualPerturbation
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput FreeDataDependence TimeHolder CriticalSourceBounds
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient hartreeDuhamelMap criticalPathIntervalSource
  CompatibleL1IntervalSource.retardedCriticalPath

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha c a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (f g : EnergyState)
  (u q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
  (hu : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u = u)
  (hq : q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
    Complex.I • E.retardedCriticalPath hDensity hSob h0 hret)
include hDensity hSob h0 hfree hret hH hab f g u q E hu hq

/-- Exact difference in the original compatible path space. -/
theorem actual_forced_difference_identity :
    u-q = (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u -
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q) +
        Complex.I • E.retardedCriticalPath hDensity hSob h0 hret := by
  exact (congrArg (fun z : CriticalPath (intervalMeasure a b) => z-q) hu.symm).trans
    (forcing_defect_algebra
      (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u)
      (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q) q
      (Complex.I • E.retardedCriticalPath hDensity hSob h0 hret) hq)

include hefree heret
/-- The endpoint witness is attached to the same literal solution difference;
the original scalar error remains L1 in time. -/
def actual_forced_difference_endpointWitness :
    EndpointGradientWitness (intervalMeasure a b) (energyPath _ (u-q)) := by
  let W := hartreeDuhamelMap_two_data_endpointWitness hDensity hSob h0 hfree hret
    hefree heret hH hab f g u q
  let V := l1RetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret E
  refine ⟨fun j => W.field j + Complex.I • V.field j, ?_⟩
  intro j
  filter_upwards [(W.add (V.smul Complex.I)).agrees j] with t ht
  have hp := actual_forced_difference_identity hDensity hSob h0 hfree hret hH hab f g u q E hu hq
  have he := congrArg (fun p : CriticalPath (intervalMeasure a b) => energyPath _ p t) hp
  simp only [map_add, map_smul, ContinuousMap.add_apply, ContinuousMap.smul_apply] at he
  exact ht.trans (Eventually.of_forall fun x =>
    congrArg (fun w : EnergyState => energyGradient j w x) he.symm)

/-- Coordinatewise estimate on the actual endpoint derivative of u-q. -/
theorem actual_forced_difference_endpoint_bound (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ (u-q) t)) ≤
      (ENNReal.ofReal (Che * ‖energyGradient j (f-g)‖) +
        ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u q).gradient j‖)) +
          ENNReal.ofReal (Cre * ‖E.gradient j‖) := by
  rw [(actual_forced_difference_endpointWitness hDensity hSob h0 hfree hret
    hefree heret hH hab f g u q E hu hq).mixedNorm_eq]
  change ‖(hartreeDuhamelMap_two_data_endpointWitness hDensity hSob h0 hfree hret
      hefree heret hH hab f g u q).field j + Complex.I •
      (l1RetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret E).field j‖ₑ ≤ _
  refine (endpoint_enorm_add_I_le (μ := intervalMeasure a b) _ _).trans (add_le_add ?_ ?_)
  · exact hartreeDuhamelMap_two_data_endpoint_enorm_bound hDensity hSob h0 hfree hret
      hefree heret hH hab f g u q j
  · exact localRetardedEndpointField_enorm_le h0 heret (E.gradient j)

/-- The literal complex Euclidean gradient difference retains the dimension
factor three from its actual coordinate assembly. -/
theorem actual_forced_complex_difference_endpoint_bound {D : ℝ}
    (hD : ∀ j : Fin 3,
      ‖(criticalPathIntervalSource hDensity hSob hH hab u q).gradient j‖ ≤ D) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) ≤
      3 * ((ENNReal.ofReal (Che * ‖f-g‖) + ENNReal.ofReal (Cre * D)) +
        ENNReal.ofReal (Cre * ‖E.gradient‖)) := by
  rw [actual_complex_difference_mixedNorm_eq]
  apply (criticalPath_complex_endpoint_le_sum (u-q)).trans
  calc
    _ ≤ ∑ _j : Fin 3, ((ENNReal.ofReal (Che * ‖f-g‖) + ENNReal.ofReal (Cre * D)) +
        ENNReal.ofReal (Cre * ‖E.gradient‖)) := Finset.sum_le_sum fun j _ =>
      (actual_forced_difference_endpoint_bound hDensity hSob h0 hfree hret hefree heret
        hH hab f g u q E hu hq j).trans (add_le_add
          (add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (energyState_gradient_norm_le (f-g) j) hefree.1))
            (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hD j) heret.1)))
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (norm_le_pi_norm E.gradient j) heret.1)))
    _ = _ := by simp [mul_add]

omit h0 hfree hret hefree heret hH hab f g E hu hq in
/-- Actual scalar S difference is supplied by time Sobolev on the same path.
The factor six is retained from the real/imaginary coordinate assembly. -/
theorem actual_scalar_difference_S_bound :
    mixedNorm (intervalMeasure a b) volume 10 10
      (fun t x => energyValue (energyPath _ u t) x - energyValue (energyPath _ q t) x) ≤
      ENNReal.ofReal ((5/3 : ℝ)*K^(1/6 : ℝ)*6) * ENNReal.ofReal ‖u-q‖ := by
  have he : mixedNorm (intervalMeasure a b) volume 10 10
      (fun t x => energyValue (energyPath _ u t) x - energyValue (energyPath _ q t) x) =
      mixedNorm (intervalMeasure a b) volume 10 10
        (fun t => (CriticalJointSources.jointFields _ u).u t -
          (CriticalJointSources.jointFields _ q).u t) := by
    apply eLpNorm_congr_ae
    filter_upwards [(CriticalJointSources.jointFields _ u).slice_eq,
      (CriticalJointSources.jointFields _ q).slice_eq] with t hut hqt
    apply eLpNorm_congr_ae
    filter_upwards [hut.1, hqt.1] with x hux hqx
    exact congrArg₂ (fun x y : ℂ => x-y) hux.symm hqx.symm
  rw [he]
  have hK := hSob.nonneg
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (5/3 : ℝ)*K^(1/6 : ℝ)),
    ENNReal.ofReal_ofNat] using joint_value_difference_critical_bound
      (intervalMeasure a b) hDensity hSob u q

end HartreeF.ActualPerturbation
