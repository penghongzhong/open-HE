import FStateSharpGroundThreshold

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal Topology
namespace HartreeF.DynamicSharpW
open EnergySpace StateEnergy StateSharpThreshold
attribute [local irreducible] energySubmodule

/-- Continuity uses exactly the native continuous linear gradient projections. -/
theorem gradientSquared_continuous : Continuous gradientSquared := by
  unfold gradientSquared
  exact continuous_finsetSum _ (fun j _ => (energyGradient j).continuous.norm.pow 2)

/-- The original strict homogeneous gradient norm comparison is exactly the
strict squared kinetic comparison, with no change in the W threshold. -/
theorem pureGradientNorm_lt_iff_gradientSquared_lt (u v : EnergyState) :
    pureGradientNorm u < pureGradientNorm v ↔ gradientSquared u < gradientSquared v := by
  unfold pureGradientNorm
  exact Real.sqrt_lt_sqrt_iff (gradientSquared_nonneg u)

/-- Taking the square root of the actual kinetic cap is the pure dotH1 cap. -/
theorem pureGradientNorm_le_of_gradientSquared_le (u : EnergyState) {C : ℝ}
    (hC : gradientSquared u ≤ C) : pureGradientNorm u ≤ Real.sqrt C := by
  exact Real.sqrt_le_sqrt hC

#print axioms gradientSquared_continuous
#print axioms pureGradientNorm_lt_iff_gradientSquared_lt
#print axioms pureGradientNorm_le_of_gradientSquared_le
end HartreeF.DynamicSharpW
