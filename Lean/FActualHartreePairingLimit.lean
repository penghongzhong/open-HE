import FWeakSourcePairingLimit
import FActualHartreeDuhamelMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.WeakSourcePairing
open EnergySpace CriticalPathSpace IntervalTimeTransport ActualDuhamelPath
open SobolevStretch StationarySelfTest ForcingDomain

attribute [local irreducible] energySubmodule criticalPathSubmodule
  criticalPathIntervalSource

/-- Actual Hartree forcing, not an arbitrary assumed compatible source, is
the left side of the limiting weak pairing. The nonlinear source and its
derivative are produced by the already verified canonical constructor. -/
theorem actual_hartree_source_pairing_limit (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b)) :
    ∀ᵐ t ∂localMeasure a b, ∀ (j : Fin 3) (φ : ℕ → Test) (h dh : L6),
      Tendsto (fun n => (φ n).toLp 6 volume) atTop (𝓝 h) →
      Tendsto (fun n => (∂_{coordinate j} (φ n)).toLp 6 volume) atTop (𝓝 dh) →
      (∫ x, forcing alpha c
        (energyValue (extendEnergyPath hab (energyPath _ u) t)) x * dh x) =
        -(∫ x, (criticalPathIntervalSource hDensity hSob hH hab u 0).gradient j t x * h x) := by
  let F := criticalPathIntervalSource hDensity hSob hH hab u 0
  filter_upwards [F.derivative,
    criticalPathIntervalSource_single_coeFn hDensity hSob hH hab u] with t hder hrep
  intro j φ h dh hφ hdφ
  have hi := source_integration_by_parts_of_schwartz_limit
    (F.value t) (F.gradient j t) (coordinate j) (hder j) φ hφ hdφ
  calc
    _ = ∫ x, F.value t x * dh x := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [show F.value t x = forcing alpha c
        (energyValue (extendEnergyPath hab (energyPath _ u) t)) x from hx]
    _ = _ := hi

#print axioms actual_hartree_source_pairing_limit
end HartreeF.WeakSourcePairing
