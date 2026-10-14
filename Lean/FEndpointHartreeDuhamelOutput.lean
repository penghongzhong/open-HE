import FEndpointFlowUpgrade
import FActualHartreeDuhamelMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace HartreeF.EndpointOutput
open MeasureTheory Filter TimeHolder EnergySpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathSpace SobolevStretch StationarySelfTest ActualStrichartz Retarded ForcingDomain
open scoped ENNReal NNReal

theorem endpoint_enorm_add_I_le {T : Type*} [MeasurableSpace T] {μ : Measure T}
    (f g : EndpointGradient μ) : ‖f + Complex.I • g‖ₑ ≤ ‖f‖ₑ + ‖g‖ₑ := by
  refine (enorm_add_le _ _).trans ?_
  rw [enorm_smul]
  have hI : ‖Complex.I‖ₑ = 1 := by simp [← ofReal_norm]
  rw [hI, one_mul]

attribute [local irreducible] criticalPathIntervalSource intervalRetardedCriticalPath
  freeCriticalPath criticalPathOfGlobalFields CriticalJointSources.jointFields
  freeCriticalPath_endpointWitness intervalRetardedCriticalPath_endpointWitness

/-- The full-Z upgrade of the same actual +i Hartree Duhamel map. Its derivative
source is the very CompatibleIntervalSource used inside hartreeDuhamelMap. -/
def hartreeDuhamelMap_endpointWitness (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u)) := by
  let Wfree := freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
    (freeEnergyState hDensity hSob (-a) u0)
  let Wret := intervalRetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret
    (criticalPathIntervalSource hDensity hSob hH hab u 0)
  refine ⟨fun j => Wfree.field j + Complex.I • Wret.field j, ?_⟩
  intro j
  filter_upwards [(Wfree.add (Wret.smul Complex.I)).agrees j] with t ht
  simpa only [EndpointGradientWitness.add, EndpointGradientWitness.smul,
    hartreeDuhamelMap, map_add, map_smul, ContinuousMap.add_apply,
    ContinuousMap.smul_apply] using ht

attribute [local irreducible] hartreeDuhamelMap

/-- Quantitative endpoint estimate for the actual same-path gradient.
The source norm is the constructed Hartree spatial-derivative norm. -/
theorem hartreeDuhamelMap_endpoint_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j
        (energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) t)) ≤
      ENNReal.ofReal (Che * ‖energyGradient j u0‖) +
        ENNReal.ofReal (Cre * ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j‖) := by
  rw [(hartreeDuhamelMap_endpointWitness hDensity hSob h0 hfree hret hefree heret hH hab u0 u).mixedNorm_eq]
  dsimp only [hartreeDuhamelMap_endpointWitness]
  change ‖(freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
      (freeEnergyState hDensity hSob (-a) u0)).field j + Complex.I •
        (intervalRetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret
          (criticalPathIntervalSource hDensity hSob hH hab u 0)).field j‖ₑ ≤ _
  refine (endpoint_enorm_add_I_le (μ := intervalMeasure a b) _ _).trans (add_le_add ?_ ?_)
  · simpa only [freeEnergyState_gradient, FreeFlow.freeL2_norm] using
      freeCriticalPath_endpoint_enorm_bound hDensity hSob hfree hefree a b
        (freeEnergyState hDensity hSob (-a) u0) j
  · exact intervalRetardedCriticalPath_endpoint_enorm_bound hDensity hSob h0 hret heret
      (criticalPathIntervalSource hDensity hSob hH hab u 0) j

/-- E and W are already coordinates of CriticalPath; this additional actual
endpoint coordinate is precisely the missing L2_t L6_x gradient condition. -/
def FullZPath {a b : ℝ} (u : CriticalPath (intervalMeasure a b)) : Prop :=
  Nonempty (EndpointGradientWitness (intervalMeasure a b) (energyPath _ u))

theorem hartreeDuhamelMap_fullZ (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    FullZPath (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u) :=
  ⟨hartreeDuhamelMap_endpointWitness hDensity hSob h0 hfree hret hefree heret hH hab u0 u⟩

/-- Once an E+W fixed point of the actual map is obtained, the same path has
the full endpoint regularity. This theorem does not assert fixed-point existence. -/
theorem fixedPoint_fullZ (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (u0 : EnergyState)
    (u : CriticalPath (intervalMeasure a b))
    (hu : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab u0 u = u) : FullZPath u := by
  rw [← hu]
  exact hartreeDuhamelMap_fullZ hDensity hSob h0 hfree hret hefree heret hH hab u0 u

end HartreeF.EndpointOutput
