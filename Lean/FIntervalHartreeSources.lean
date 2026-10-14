import FIntervalScalarSource
import FIntervalNestedLpTransport
import FCompatibleIntervalSource
import FCriticalPathGradientSource
import FEndpointSourceWeakDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace LocalScalarSource ForcingDomain TimeHolder
open CriticalJointSources CriticalTimeSobolev SobolevStretch StationarySelfTest Retarded
open GradientMajorants WeakHartreeProduct
attribute [local irreducible] jointFields

/-- The true scalar and vector nonlinear source are constructed from two
CriticalPaths, using the same C43-to-C42 joint representatives throughout. -/
def criticalPathIntervalSource (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (u v : CriticalPath (intervalMeasure a b)) : CompatibleIntervalSource a b := by
  let μ := intervalMeasure a b
  let r := jointFields μ u
  let q := jointFields μ v
  let Gs : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 μ := Classical.choose (exists_joint_actualGradient_source μ hDensity hSob hH u v)
  have hGs := (Classical.choose_spec (exists_joint_actualGradient_source μ hDensity hSob hH u v)).1
  let G := toLocalLp hab 2 Gs
  let F := intervalScalarSource hab hH u - intervalScalarSource hab hH v
  have hF := intervalScalarDifferenceSource_coeFn hab hH u v r.u q.u
    (r.slice_eq.mono fun _ ht => ht.1) (q.slice_eq.mono fun _ ht => ht.1)
  have hG : ∀ᵐ t ∂localMeasure a b, ∀ᵐ x ∂(volume : Measure Space),
      G t x = actualFullGradient alpha c (r.u (Set.projIcc a b hab t))
        (r.U (Set.projIcc a b hab t)) (r.V (Set.projIcc a b hab t)) x -
      actualFullGradient alpha c (q.u (Set.projIcc a b hab t))
        (q.U (Set.projIcc a b hab t)) (q.V (Set.projIcc a b hab t)) x := by
    filter_upwards [toLocalLp_nested_coeFn hab 2 (ENNReal.ofReal (6/5 : ℝ)) volume Gs,
      ae_clamp hab hGs] with t ht hs
    exact Filter.EventuallyEq.trans ht hs
  have hSlices := ae_clamp hab (joint_slices μ hDensity hSob u v)
  have hd := actual_endpointSource_tempered_derivatives hDensity hSob hH (localMeasure a b)
    (fun t => r.u (Set.projIcc a b hab t)) (fun t => q.u (Set.projIcc a b hab t))
    (fun t => r.U (Set.projIcc a b hab t)) (fun t => r.V (Set.projIcc a b hab t))
    (fun t => q.U (Set.projIcc a b hab t)) (fun t => q.V (Set.projIcc a b hab t))
    hSlices F G hF hG
  exact ⟨F, fun j => endpointGradientCoordinateSource (localMeasure a b) j G, hd⟩

@[simp] theorem criticalPathIntervalSource_value (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u v : CriticalPath (intervalMeasure a b)) :
    (criticalPathIntervalSource hDensity hSob hH hab u v).value =
      intervalScalarSource hab hH u - intervalScalarSource hab hH v := rfl

/-- Canonical-value identity for the produced source, independent of C42's choices. -/
theorem criticalPathIntervalSource_value_coeFn (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u v : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b, ∀ᵐ x ∂(volume : Measure Space),
      (criticalPathIntervalSource hDensity hSob hH hab u v).value t x =
        forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ u) t)) x -
          forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ v) t)) x := by
  exact intervalScalarDifferenceSource_coeFn hab hH u v
    (fun t => energyValue (energyPath _ u t)) (fun t => energyValue (energyPath _ v t))
    (Eventually.of_forall fun _ => EventuallyEq.rfl) (Eventually.of_forall fun _ => EventuallyEq.rfl)

end HartreeF.ActualDuhamelPath
