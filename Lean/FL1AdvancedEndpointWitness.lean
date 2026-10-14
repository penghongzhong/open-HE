import FL1AdvancedIdentification

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain
open SobolevStretch StationarySelfTest Retarded ActualStrichartz
open BackwardUniformData EndpointOutput ActualBackwardLocalFixedPoint
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energyPath energyGradient criticalGradient freeCriticalPath
  CompatibleL1IntervalSource.advancedCriticalPath
  CompatibleL1IntervalSource.retardedCriticalPath intervalAdvancedCriticalPath

/-- Exact terminal transport of the previously accepted L2 advanced path. -/
theorem intervalAdvancedCriticalPath_terminal_transport (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hab : a ≤ b) (F : CompatibleIntervalSource a b) :
    intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F =
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b)
        (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 hret F) ⟨b,hab,le_rfl⟩)) -
      intervalRetardedCriticalPath hDensity hSob h0 hret F := by
  let D := intervalTotalSourceEnergy hDensity hSob h0 F
  have ht := intervalAdvancedCriticalPath_terminal hDensity hSob h0 hfree hret hab F
  unfold intervalAdvancedCriticalPath at ht ⊢
  rw [criticalPath_energy_sub_apply, freeCriticalPath_energy] at ht
  have he := sub_eq_zero.mp ht
  have hd : D = freeEnergyState hDensity hSob (-b)
      (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 hret F) ⟨b,hab,le_rfl⟩) := by
    rw [← he, ← freeEnergyState_add_time, neg_add_cancel, freeEnergyState_zero_time]
  exact congrArg (fun d : EnergyState => freeCriticalPath hDensity hSob hfree a b d -
    intervalRetardedCriticalPath hDensity hSob h0 hret F) hd

/-- Continuity of the genuine terminal free path follows from its accepted data bound. -/
theorem backwardFreeCriticalPath_tendsto (hDensity : OrdinaryH1Density)
    {K Ch a b : ℝ} (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    {f : ℕ → EnergyState} {g : EnergyState} (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-b) (f n))) atTop
      (𝓝 (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) g))) := by
  apply l1_extension_tendsto_of_norm_sub (V := CriticalPath (intervalMeasure a b))
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => actual_backwardFreeCriticalPath_difference_norm hDensity hSob hfree a b (f n) g)
  simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hf)

namespace CompatibleL1IntervalSource
variable {a b : ℝ} (E : CompatibleL1IntervalSource a b)

/-- Actual advanced L1 path equals free terminal transport of R(E)(b) minus R(E). -/
theorem advancedCriticalPath_terminal_transport (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hab : a ≤ b) :
    E.advancedCriticalPath hDensity hSob h0 hfree hret =
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b)
        (energyPath _ (E.retardedCriticalPath hDensity hSob h0 hret) ⟨b,hab,le_rfl⟩)) -
      E.retardedCriticalPath hDensity hSob h0 hret := by
  have ht := E.advanced_approximation_tendsto hDensity hSob h0 hfree hret
  simp only [intervalAdvancedCriticalPath_terminal_transport hDensity hSob h0 hfree hret hab] at ht
  exact tendsto_nhds_unique ht
    (l1_extension_tendsto_sub (V := CriticalPath (intervalMeasure a b))
      (backwardFreeCriticalPath_tendsto hDensity hSob hfree
      (E.retarded_approximation_energy_tendsto hDensity hSob h0 hret ⟨b,hab,le_rfl⟩))
      (E.retarded_approximation_tendsto hDensity hSob h0 hret))

/-- The endpoint witness belongs to the same canonical advanced path. -/
def advancedCriticalPath_endpointWitness (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hab : a ≤ b) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (E.advancedCriticalPath hDensity hSob h0 hfree hret)) := by
  let W := freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
    (freeEnergyState hDensity hSob (-b)
      (energyPath _ (E.retardedCriticalPath hDensity hSob h0 hret) ⟨b,hab,le_rfl⟩))
  let V := l1RetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret E
  refine ⟨fun j => W.field j - V.field j, ?_⟩
  intro j
  filter_upwards [(subtractEndpointWitnesses W V).agrees j] with t ht
  have he := congrArg (fun p : CriticalPath (intervalMeasure a b) => energyPath _ p t)
    (E.advancedCriticalPath_terminal_transport hDensity hSob h0 hfree hret hab)
  rw [criticalPath_energy_sub_apply] at he
  exact ht.trans (Eventually.of_forall fun x =>
    congrArg (fun w : EnergyState => energyGradient j w x) he.symm)

/-- The derived advanced endpoint constant is Che*C0+Cre, with no scalar L2 input. -/
theorem advancedCriticalPath_endpoint_enorm_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hab : a ≤ b) (j : Fin 3) :
    ‖(E.advancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret hefree heret hab).field j‖ₑ ≤
      ENNReal.ofReal ((Che*C0+Cre)*‖E.gradient j‖) := by
  let R := E.retardedCriticalPath hDensity hSob h0 hret
  have hb : ‖energyGradient j (freeEnergyState hDensity hSob (-b)
      (energyPath _ R ⟨b,hab,le_rfl⟩))‖ ≤ C0*‖E.gradient j‖ := by
    rw [freeEnergyState_gradient, FreeFlow.freeL2_norm,
      l1RetardedCriticalPath_actual_gradient hDensity hSob h0 hret E]
    simpa only [extendEndpointSource_norm] using retardedL2_norm h0
      (extendEndpointSource (Set.Icc a b) measurableSet_Icc (E.gradient j)) b
  have hf := (freeCriticalPath_endpoint_enorm_bound hDensity hSob hfree hefree a b
    (freeEnergyState hDensity hSob (-b) (energyPath _ R ⟨b,hab,le_rfl⟩)) j).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb hefree.1))
  have hr := localRetardedEndpointField_enorm_le h0 heret (E.gradient j)
  change ‖(freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
    (freeEnergyState hDensity hSob (-b) (energyPath _ R ⟨b,hab,le_rfl⟩))).field j -
      (l1RetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret E).field j‖ₑ ≤ _
  apply enorm_sub_le.trans ((add_le_add hf hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (mul_nonneg hefree.1 (mul_nonneg h0.1 (norm_nonneg _))) (mul_nonneg heret.1 (norm_nonneg _))]
  congr 1
  ring

end CompatibleL1IntervalSource
end HartreeF.ActualDuhamelPath
