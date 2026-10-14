import FActualBackwardForcedStability
import FL1AdvancedEndpointWitness
import FActualForcedEndpointDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.BackwardPerturbation
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput FreeDataDependence TimeHolder CriticalSourceBounds
open ActualBackwardLocalFixedPoint BackwardUniformData ActualPerturbation
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  backwardHartreeDuhamelMap criticalPathIntervalSource intervalAdvancedCriticalPath
  freeCriticalPath freeEnergyState CompatibleL1IntervalSource.advancedCriticalPath

/-- Quantitative endpoint norm of the accepted L2 advanced path witness. -/
theorem intervalAdvanced_endpoint_enorm_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (F : CompatibleIntervalSource a b) (j : Fin 3) :
    ‖(intervalAdvancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret hefree heret F).field j‖ₑ ≤
      ENNReal.ofReal ((Che*C0+Cre)*‖F.gradient j‖) := by
  have hg : ‖energyGradient j (intervalTotalSourceEnergy hDensity hSob h0 F)‖ ≤ C0*‖F.gradient j‖ := by
    unfold intervalTotalSourceEnergy
    rw [restrictedEnergyState_gradient]
    exact restrictedL2_extend_norm h0 (Set.Icc a b) measurableSet_Icc
      (F.gradient j) (Set.Ioc a b) measurableSet_Ioc 0
  have hf := (freeCriticalPath_endpoint_enorm_bound hDensity hSob hfree hefree a b
    (intervalTotalSourceEnergy hDensity hSob h0 F) j).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hg hefree.1))
  have hr := intervalRetardedCriticalPath_endpoint_enorm_bound hDensity hSob h0 hret heret F j
  change ‖(freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
      (intervalTotalSourceEnergy hDensity hSob h0 F)).field j -
      (intervalRetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret F).field j‖ₑ ≤ _
  apply enorm_sub_le.trans ((add_le_add hf hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (mul_nonneg hefree.1 (mul_nonneg h0.1 (norm_nonneg _)))
    (mul_nonneg heret.1 (norm_nonneg _))]
  congr 1
  ring

section Abstract
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
theorem endpoint_enorm_sub_I_le (x y : X) : ‖x-Complex.I • y‖ₑ ≤ ‖x‖ₑ+‖y‖ₑ := by
  refine enorm_sub_le.trans ?_
  rw [enorm_smul]
  have hi : ‖Complex.I‖ₑ=1 := by simp [← ofReal_norm]
  rw [hi, one_mul]
theorem complexDecrement_two_data_sub (x y z w : X) :
    (x-Complex.I • y)-(z-Complex.I • w)=(x-z)-Complex.I • (y-w) := by
  rw [smul_sub]
  abel
end Abstract

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha c a b : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (f g : EnergyState)
  (u q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)
  (hu : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u = u)
  (hq : q = backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q +
    Complex.I • E.advancedCriticalPath hDensity hSob h0 hfree hret)
include hDensity hSob h0 hfree hret hH hab f g u q E hu hq

/-- Exact solution difference with the negative-i future source and negative-i error. -/
theorem actual_backward_forced_difference_identity :
    u-q = (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) (f-g)) -
      Complex.I • intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
        (criticalPathIntervalSource hDensity hSob hH hab u q)) -
      Complex.I • E.advancedCriticalPath hDensity hSob h0 hfree hret := by
  let P := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
  let A : CompatibleIntervalSource a b → CriticalPath (intervalMeasure a b) :=
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
  let F := criticalPathIntervalSource hDensity hSob hH hab
  have hs : A (F u 0)-A (F q 0)=A (F u q) :=
    (intervalAdvancedCriticalPath_sub hDensity hSob h0 hfree hret (F u 0) (F q 0)).symm.trans
      (congrArg A (criticalPathIntervalSource_sub_zero hDensity hSob hH hab u q))
  have hp : P f u-P g q =
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) (f-g)) -
        Complex.I • A (F u q) := by
    have halg : P f u-P g q =
        (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) f) -
          freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) g)) -
          Complex.I • (A (F u 0)-A (F q 0)) := by
      dsimp only [P]
      unfold backwardHartreeDuhamelMap
      exact complexDecrement_two_data_sub
        (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) f))
        (A (F u 0))
        (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) g))
        (A (F q 0))
    exact halg.trans (congrArg₂ (fun x y : CriticalPath (intervalMeasure a b) => x-Complex.I • y)
      (actual_backwardFreeCriticalPath_sub hDensity hSob hfree a b f g) hs)
  have he : u-q=(P f u-P g q)-Complex.I • E.advancedCriticalPath hDensity hSob h0 hfree hret :=
    (congrArg₂ (fun x y : CriticalPath (intervalMeasure a b) => x-y) hu.symm hq).trans
      (sub_add_eq_sub_sub (P f u) (P g q) (Complex.I • E.advancedCriticalPath hDensity hSob h0 hfree hret))
  exact he.trans (congrArg (fun x : CriticalPath (intervalMeasure a b) =>
    x-Complex.I • E.advancedCriticalPath hDensity hSob h0 hfree hret) hp)

include hefree heret
/-- Full endpoint witness of the literal backward solution difference. -/
def actual_backward_forced_difference_endpointWitness :
    EndpointGradientWitness (intervalMeasure a b) (energyPath _ (u-q)) := by
  let W := freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
    (freeEnergyState hDensity hSob (-b) (f-g))
  let V := intervalAdvancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret hefree heret
    (criticalPathIntervalSource hDensity hSob hH hab u q)
  let T := E.advancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret hefree heret hab
  refine ⟨fun j => (W.field j-Complex.I • V.field j)-Complex.I • T.field j, ?_⟩
  intro j
  filter_upwards [(subtractEndpointWitnesses (subtractEndpointWitnesses W (V.smul Complex.I))
    (T.smul Complex.I)).agrees j] with t ht
  have hp := actual_backward_forced_difference_identity hDensity hSob h0 hfree hret hH hab f g u q E hu hq
  have he : energyPath (intervalMeasure a b) (u-q) t =
      (energyPath _ (freeCriticalPath hDensity hSob hfree a b
        (freeEnergyState hDensity hSob (-b) (f-g))) t -
        Complex.I • energyPath _ (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
          (criticalPathIntervalSource hDensity hSob hH hab u q)) t) -
      Complex.I • energyPath _ (E.advancedCriticalPath hDensity hSob h0 hfree hret) t := by
    simpa only [criticalPath_energy_sub_apply, criticalPath_energy_smul_apply] using
      congrArg (fun p : CriticalPath (intervalMeasure a b) => energyPath (intervalMeasure a b) p t) hp
  exact ht.trans (Eventually.of_forall fun x =>
    congrArg (fun w : EnergyState => energyGradient j w x) he.symm)

/-- Coordinate estimate retains the actual advanced endpoint coefficient. -/
theorem actual_backward_forced_difference_endpoint_bound (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ (u-q) t)) ≤
      (ENNReal.ofReal (Che*‖energyGradient j (f-g)‖) +
        ENNReal.ofReal ((Che*C0+Cre)*‖(criticalPathIntervalSource hDensity hSob hH hab u q).gradient j‖)) +
        ENNReal.ofReal ((Che*C0+Cre)*‖E.gradient j‖) := by
  rw [(actual_backward_forced_difference_endpointWitness hDensity hSob h0 hfree hret
    hefree heret hH hab f g u q E hu hq).mixedNorm_eq]
  change ‖((freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
      (freeEnergyState hDensity hSob (-b) (f-g))).field j - Complex.I •
      (intervalAdvancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret hefree heret
        (criticalPathIntervalSource hDensity hSob hH hab u q)).field j) - Complex.I •
      (E.advancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret hefree heret hab).field j‖ₑ ≤ _
  refine (endpoint_enorm_sub_I_le _ _).trans (add_le_add
    ((endpoint_enorm_sub_I_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · simpa only [freeEnergyState_gradient, FreeFlow.freeL2_norm] using
      freeCriticalPath_endpoint_enorm_bound hDensity hSob hfree hefree a b
        (freeEnergyState hDensity hSob (-b) (f-g)) j
  · exact intervalAdvanced_endpoint_enorm_bound hDensity hSob h0 hfree hret hefree heret _ j
  · exact E.advancedCriticalPath_endpoint_enorm_bound hDensity hSob h0 hfree hret hefree heret hab j

/-- The Euclidean gradient assembly retains dimension factor three. -/
theorem actual_backward_forced_complex_difference_endpoint_bound {D : ℝ}
    (hD : ∀ j : Fin 3, ‖(criticalPathIntervalSource hDensity hSob hH hab u q).gradient j‖ ≤ D) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x-energyComplexGradient (energyPath _ q t) x) ≤
      3*((ENNReal.ofReal (Che*‖f-g‖)+ENNReal.ofReal ((Che*C0+Cre)*D))+
        ENNReal.ofReal ((Che*C0+Cre)*‖E.gradient‖)) := by
  have hC : 0 ≤ Che*C0+Cre := add_nonneg (mul_nonneg hefree.1 h0.1) heret.1
  rw [actual_complex_difference_mixedNorm_eq]
  apply (criticalPath_complex_endpoint_le_sum (u-q)).trans
  calc
    _ ≤ ∑ _j : Fin 3, ((ENNReal.ofReal (Che*‖f-g‖)+ENNReal.ofReal ((Che*C0+Cre)*D))+
        ENNReal.ofReal ((Che*C0+Cre)*‖E.gradient‖)) := Finset.sum_le_sum fun j _ =>
      (actual_backward_forced_difference_endpoint_bound hDensity hSob h0 hfree hret hefree heret
        hH hab f g u q E hu hq j).trans (add_le_add
          (add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (energyState_gradient_norm_le (f-g) j) hefree.1))
            (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hD j) hC)))
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (norm_le_pi_norm E.gradient j) hC)))
    _ = _ := by simp [mul_add]

end HartreeF.BackwardPerturbation
