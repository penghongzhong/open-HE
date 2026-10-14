import FEnergyGradientTopology
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.EnergySpace
open SobolevStretch

attribute [local irreducible] energySubmodule

/-- Upgrade the derivatives of all three genuine L2 gradient coordinates to
the actual Banach derivative. The derivative state must already exist. -/
theorem hasDerivAt_of_gradient_hasDerivAt {K : ℝ} (hSob : OrdinarySobolev K)
    {u : ℝ → EnergyState} {du : EnergyState} {t : ℝ}
    (h : ∀ j : Fin 3, HasDerivAt (fun s => energyGradient j (u s))
      (energyGradient j du) t) : HasDerivAt u du t := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_of_gradientTendsto hSob
  intro j
  have hj := (h j).tendsto_slope_zero
  change Tendsto (fun n : ℝ => ((energyGradient j).restrictScalars ℝ)
    (n⁻¹ • (u (t+n) - u t))) (𝓝[≠] 0) (𝓝 (energyGradient j du))
  simpa only [map_smul, map_sub, ContinuousLinearMap.coe_restrictScalars'] using hj

theorem hasDerivAt_iff_gradient_hasDerivAt {K : ℝ} (hSob : OrdinarySobolev K)
    {u : ℝ → EnergyState} {du : EnergyState} {t : ℝ} :
    HasDerivAt u du t ↔ ∀ j : Fin 3, HasDerivAt (fun s => energyGradient j (u s))
      (energyGradient j du) t := by
  constructor
  · intro hu j
    exact ((energyGradient j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu
  · exact hasDerivAt_of_gradient_hasDerivAt hSob

#print axioms hasDerivAt_of_gradient_hasDerivAt
#print axioms hasDerivAt_iff_gradient_hasDerivAt
end HartreeF.EnergySpace
