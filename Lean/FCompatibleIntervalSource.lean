import FIntervalTimeTransport
import FEndpointTimeExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter LineDeriv
namespace HartreeF.ActualDuhamelPath
open IntervalTimeTransport EnergySpace Retarded

/-- A compatible local input source. The nonlinear constructor below produces
this data, before any retarded output is requested. -/
structure CompatibleIntervalSource (a b : ℝ) where
  value : LocalEndpointSource (Set.Icc a b)
  gradient : Fin 3 → LocalEndpointSource (Set.Icc a b)
  derivative : ∀ᵐ t ∂localMeasure a b, ∀ j : Fin 3,
    ∂_{coordinate j} (Lp.toTemperedDistribution (value t)) =
      Lp.toTemperedDistribution (gradient j t)

end HartreeF.ActualDuhamelPath
