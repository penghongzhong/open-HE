import FActualGradientPathContinuity
import FActualIntervalSourceBounds
import FCompatibleIntervalSourceDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace HartreeF.CriticalSourceBounds
open EnergySpace CriticalPathSpace TimeHolder SobolevStretch StationarySelfTest
open ForcingDomain ActualDuhamelPath IntervalTimeTransport Retarded

/-- Abstract conversion from a vanishing difference majorant to continuity. -/
theorem continuous_of_enorm_sub_le_tendsto
    {X Y : Type*} [TopologicalSpace X] [NormedAddCommGroup Y]
    (f : X → Y) (a : X → X → ℝ≥0∞)
    (hbound : ∀ z w, ‖f z-f w‖ₑ ≤ a z w)
    (ha : ∀ w, Tendsto (fun z => a z w) (𝓝 w) (𝓝 0)) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro w
  apply tendsto_iff_enorm_sub_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (ha w)
    (fun _ => bot_le) (fun z => hbound z w)

attribute [local irreducible] criticalPathIntervalSource
  energySubmodule criticalPathSubmodule
attribute [local instance] endpointSourceExponent_one_le

/-- The actual constructed coordinate-source difference is controlled by the
full-gradient mixed norm, using the accepted source subtraction identity. -/
theorem criticalPathIntervalSource_gradient_difference_enorm_le
    (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
    (u v : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j -
      (criticalPathIntervalSource hDensity hSob hH hab v 0).gradient j‖ₑ ≤
      actualGradientSize (intervalMeasure a b) alpha c u v := by
  have hs := congrArg (fun F : CompatibleIntervalSource a b => F.gradient j)
    (criticalPathIntervalSource_sub_zero hDensity hSob hH hab u v)
  have he :
      (criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j -
        (criticalPathIntervalSource hDensity hSob hH hab v 0).gradient j =
      (criticalPathIntervalSource hDensity hSob hH hab u v).gradient j := by
    simpa only [CompatibleIntervalSource.sub, Pi.sub_apply] using hs
  exact (congrArg (fun G : LocalEndpointSource (Set.Icc a b) => ‖G‖ₑ) he).le.trans
    (criticalPathIntervalSource_gradient_enorm_le hDensity hSob hH hab u v j)

/-- Each coordinate of the actual zero-comparison interval source is continuous
in the complete E+W CriticalPath topology. -/
theorem criticalPathIntervalSource_gradient_continuous
    (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (j : Fin 3) :
    Continuous (fun u : CriticalPath (intervalMeasure a b) =>
      (criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j) :=
  continuous_of_enorm_sub_le_tendsto
    (fun u => (criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j)
    (actualGradientSize (intervalMeasure a b) alpha c)
    (fun u v => criticalPathIntervalSource_gradient_difference_enorm_le hDensity hSob hH hab u v j)
    (fun w => actualGradientSize_tendsto_zero (intervalMeasure a b) hDensity hSob hH
      (fun u => u) w tendsto_id)

theorem criticalPathIntervalSource_gradient_tendsto
    (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (j : Fin 3)
    {I : Type*} {l : Filter I} (u : I → CriticalPath (intervalMeasure a b))
    (v : CriticalPath (intervalMeasure a b)) (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun i => (criticalPathIntervalSource hDensity hSob hH hab (u i) 0).gradient j)
      l (𝓝 ((criticalPathIntervalSource hDensity hSob hH hab v 0).gradient j)) :=
  ((criticalPathIntervalSource_gradient_continuous hDensity hSob hH hab j).tendsto v).comp hu

#print axioms continuous_of_enorm_sub_le_tendsto
#print axioms criticalPathIntervalSource_gradient_difference_enorm_le
#print axioms criticalPathIntervalSource_gradient_continuous
#print axioms criticalPathIntervalSource_gradient_tendsto
end HartreeF.CriticalSourceBounds
