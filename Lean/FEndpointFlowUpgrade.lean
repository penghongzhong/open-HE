import FEndpointGradientWitness
import FIntervalRetardedPath

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.EndpointOutput
open MeasureTheory Filter LineDeriv TimeHolder EnergySpace ActualDuhamelPath IntervalTimeTransport
open CriticalPathSpace SobolevStretch StationarySelfTest ActualStrichartz Retarded
open scoped ENNReal NNReal

def freeCriticalPath_endpointWitness (hDensity : OrdinaryH1Density) {K C Ce : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (he : OrdinaryHomogeneousEndpointOutput Ce) (a b : ℝ) (u : EnergyState) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (freeCriticalPath hDensity hSob h a b u)) :=
  intervalEndpointWitness a b (fun t => freeEnergyState hDensity hSob t u)
    (fun j => freeJoint (energyGradient j u))
    (fun j => freeJoint_stronglyMeasurable (energyGradient j u))
    (fun j => freeJoint_endpoint_finite he (energyGradient j u))
    (freeJoint_energyGradient hDensity hSob u)

theorem freeCriticalPath_endpoint_enorm_bound (hDensity : OrdinaryH1Density) {K C Ce : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryHomogeneousStrichartz C)
    (he : OrdinaryHomogeneousEndpointOutput Ce) (a b : ℝ) (u : EnergyState) (j : Fin 3) :
    ‖(freeCriticalPath_endpointWitness hDensity hSob h he a b u).field j‖ₑ ≤
      ENNReal.ofReal (Ce * ‖energyGradient j u‖) :=
  (intervalEndpointField_enorm_le a b (freeJoint (energyGradient j u))
    (freeJoint_stronglyMeasurable (energyGradient j u))
    (freeJoint_endpoint_finite he (energyGradient j u))).trans (he.2 _)

def retardedCriticalPath_endpointWitness (hDensity : OrdinaryH1Density) {K C0 C Ce : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (he : OrdinaryRetardedEndpointOutput h0 Ce)
    (a b : ℝ) (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s)) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (retardedCriticalPath hDensity hSob h0 h a b F G hFG)) :=
  intervalEndpointWitness a b (retardedEnergyState hDensity hSob h0 F G hFG)
    (fun j => retardedJoint h0 (G j))
    (fun j => retardedJoint_stronglyMeasurable h0 (G j))
    (fun j => retardedJoint_endpoint_finite h0 he (G j))
    (retardedJoint_energyGradient hDensity hSob h0 F G hFG)

theorem retardedCriticalPath_endpoint_enorm_bound (hDensity : OrdinaryH1Density)
    {K C0 C Ce : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (he : OrdinaryRetardedEndpointOutput h0 Ce)
    (a b : ℝ) (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (j : Fin 3) :
    ‖(retardedCriticalPath_endpointWitness hDensity hSob h0 h he a b F G hFG).field j‖ₑ ≤
      ENNReal.ofReal (Ce * ‖G j‖) :=
  (intervalEndpointField_enorm_le a b (retardedJoint h0 (G j))
    (retardedJoint_stronglyMeasurable h0 (G j))
    (retardedJoint_endpoint_finite h0 he (G j))).trans (he.2 _)

/-- The zero-extended derivative source is exactly the derivative source used
to construct this retarded CriticalPath. No substitute derivative field occurs. -/
def intervalRetardedCriticalPath_endpointWitness (hDensity : OrdinaryH1Density)
    {K C0 C Ce a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (he : OrdinaryRetardedEndpointOutput h0 Ce)
    (F : CompatibleIntervalSource a b) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h F)) :=
  retardedCriticalPath_endpointWitness hDensity hSob h0 h he a b
    (extendEndpointSource (Set.Icc a b) measurableSet_Icc F.value)
    (fun j => extendEndpointSource (Set.Icc a b) measurableSet_Icc (F.gradient j))
    (ae_all_iff.mp (extendEndpointSource_coordinate_derivatives (Set.Icc a b)
      measurableSet_Icc F.value F.gradient F.derivative))

theorem intervalRetardedCriticalPath_endpoint_enorm_bound (hDensity : OrdinaryH1Density)
    {K C0 C Ce a b : ℝ} (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (he : OrdinaryRetardedEndpointOutput h0 Ce)
    (F : CompatibleIntervalSource a b) (j : Fin 3) :
    ‖(intervalRetardedCriticalPath_endpointWitness hDensity hSob h0 h he F).field j‖ₑ ≤
      ENNReal.ofReal (Ce * ‖F.gradient j‖) := by
  unfold intervalRetardedCriticalPath_endpointWitness
  simpa only [extendEndpointSource_norm] using
    retardedCriticalPath_endpoint_enorm_bound hDensity hSob h0 h he a b
      (extendEndpointSource (Set.Icc a b) measurableSet_Icc F.value)
      (fun k => extendEndpointSource (Set.Icc a b) measurableSet_Icc (F.gradient k))
      (ae_all_iff.mp (extendEndpointSource_coordinate_derivatives (Set.Icc a b)
        measurableSet_Icc F.value F.gradient F.derivative)) j

end HartreeF.EndpointOutput
