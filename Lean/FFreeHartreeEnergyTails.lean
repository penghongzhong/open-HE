import FFreeHomogeneousL6Decay
import FStateEnergyCalculus

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.FreeTimeDecay
open EnergySpace SobolevStretch StationarySelfTest ActualStrichartz
open EnergyVariation StateEnergy ForcingDomain

/-- Zero in the canonical L6 quotient has zero literal Hartree interaction. -/
theorem interactionLp_zero {alpha : ℝ} (ha : 0<alpha) : interactionLp alpha 0=0 := by
  have he : DirectionalCoercivity.interaction alpha (0 : Space → ℂ)=0 := by
    unfold DirectionalCoercivity.interaction powerDensity
    simp only [Pi.zero_apply, norm_zero, Real.zero_rpow (by linarith : 3+alpha≠0), mul_zero, integral_zero]
  exact (interaction_congr_ae alpha (Lp.coeFn_zero ℂ 6 volume)).trans he

/-- Actual L6 decay removes the nonlocal interaction by the proved Hartree continuity. -/
theorem interactionLp_tendsto_zero_of_value_norm {alpha : ℝ}
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {l : Filter ℝ} {g : ℝ → EnergyState}
    (hg : Tendsto (fun t => ‖energyValue (g t)‖) l (𝓝 0)) :
    Tendsto (fun t => interactionLp alpha (energyValue (g t))) l (𝓝 0) := by
  have ht := (interactionLp_contDiff_one hOrd).continuous.continuousAt.tendsto.comp
    (tendsto_zero_iff_norm_tendsto_zero.mpr hg)
  simpa only [Function.comp_def, interactionLp_zero hOrd.order_pos] using ht

/-- The divergent positive-time free profile contributes no Hartree interaction. -/
theorem freeEnergyState_interaction_tendsto_zero_atTop (hDensity : OrdinaryH1Density)
    {alpha K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha)) (u : EnergyState) :
    Tendsto (fun t => interactionLp alpha (energyValue (freeEnergyState hDensity hSob t u)))
      atTop (𝓝 0) :=
  interactionLp_tendsto_zero_of_value_norm hOrd
    (freeEnergyState_value_norm_tendsto_zero_atTop hDensity hSob hS u)

/-- The divergent negative-time free profile contributes no Hartree interaction. -/
theorem freeEnergyState_interaction_tendsto_zero_atBot (hDensity : OrdinaryH1Density)
    {alpha K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha)) (u : EnergyState) :
    Tendsto (fun t => interactionLp alpha (energyValue (freeEnergyState hDensity hSob t u)))
      atBot (𝓝 0) :=
  interactionLp_tendsto_zero_of_value_norm hOrd
    (freeEnergyState_value_norm_tendsto_zero_atBot hDensity hSob hS u)

/-- Free total energy tends to the fixed kinetic half, rather than being conserved. -/
theorem freeEnergyState_totalEnergy_tendsto_kinetic_atTop (hDensity : OrdinaryH1Density)
    {alpha K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha)) (u : EnergyState) :
    Tendsto (fun t => totalEnergy alpha (freeEnergyState hDensity hSob t u))
      atTop (𝓝 (gradientSquared u/2)) := by
  have ht := (tendsto_const_nhds (x := gradientSquared u/2)).sub
    ((freeEnergyState_interaction_tendsto_zero_atTop hDensity hSob hS hOrd u).div_const (2*(3+alpha)))
  simpa only [totalEnergy, freeEnergyState_gradientSquared, zero_div, sub_zero] using ht

/-- Negative-time total energy has the same actual kinetic limit. -/
theorem freeEnergyState_totalEnergy_tendsto_kinetic_atBot (hDensity : OrdinaryH1Density)
    {alpha K C : ℝ} (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha)) (u : EnergyState) :
    Tendsto (fun t => totalEnergy alpha (freeEnergyState hDensity hSob t u))
      atBot (𝓝 (gradientSquared u/2)) := by
  have ht := (tendsto_const_nhds (x := gradientSquared u/2)).sub
    ((freeEnergyState_interaction_tendsto_zero_atBot hDensity hSob hS hOrd u).div_const (2*(3+alpha)))
  simpa only [totalEnergy, freeEnergyState_gradientSquared, zero_div, sub_zero] using ht

#print axioms interactionLp_zero
#print axioms interactionLp_tendsto_zero_of_value_norm
#print axioms freeEnergyState_interaction_tendsto_zero_atTop
#print axioms freeEnergyState_interaction_tendsto_zero_atBot
#print axioms freeEnergyState_totalEnergy_tendsto_kinetic_atTop
#print axioms freeEnergyState_totalEnergy_tendsto_kinetic_atBot
end HartreeF.FreeTimeDecay
