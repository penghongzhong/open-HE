import FFreeHartreeEnergyTails
import FBoundedEnergyContinuity
import FActualMaximalMildEnergyConservation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology

namespace HartreeF.WaveRealization
open EnergySpace EnergyVariation StateEnergy FreeTimeDecay MaximalTrajectory
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain EndpointOutput
open Regularization.Actual
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule

/-- Energy of the same actual mild trajectory is determined by its free
asymptote. Bounds and a sequence inside its domain suffice; no energy identity
or vanishing potential is assumed. -/
theorem totalEnergy_of_actual_free_asymptote (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha s0 B : ℝ} {u0 : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (M : LocalMildTrajectory alpha (HeatRiesz.standardRieszConstant alpha) s0 u0)
    (phi : EnergyState) (l : Filter ℝ) (seq : ℕ → ℝ)
    (hseq : Tendsto seq atTop l)
    (hseqDom : ∀ n, seq n ∈ M.domain) (hseqCap : ∀ n, ‖M.state (seq n)‖ ≤ B)
    (hasymptote : Tendsto (fun t => ‖M.state t-freeEnergyState hDensity hSob t phi‖) l (𝓝 0))
    (hfree6 : Tendsto (fun t => ‖energyValue (freeEnergyState hDensity hSob t phi)‖) l (𝓝 0)) :
    ∀ t ∈ M.domain, totalEnergy alpha (M.state t) = gradientSquared phi/2 := by
  have hvalue : Tendsto (fun t => ‖energyValue (M.state t)‖) l (𝓝 0) := by
    have hsum : Tendsto (fun t =>
        ‖M.state t-freeEnergyState hDensity hSob t phi‖ +
        ‖energyValue (freeEnergyState hDensity hSob t phi)‖) l (𝓝 0) := by
      simpa only [add_zero] using hasymptote.add hfree6
    apply squeeze_zero (fun t => norm_nonneg _) ?_ hsum
    intro t
    have hd : ‖energyValue (M.state t)-energyValue (freeEnergyState hDensity hSob t phi)‖ ≤
        ‖M.state t-freeEnergyState hDensity hSob t phi‖ := by
      have hh := energyState_value_norm_le (M.state t-freeEnergyState hDensity hSob t phi)
      change ‖energyValue (M.state t-freeEnergyState hDensity hSob t phi)‖ ≤ _ at hh
      rwa [map_sub] at hh
    exact (norm_le_norm_sub_add (energyValue (M.state t))
      (energyValue (freeEnergyState hDensity hSob t phi))).trans (add_le_add hd le_rfl)
  have hpot := interactionLp_tendsto_zero_of_value_norm hH hvalue
  let Cfree : ℝ := (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) * ‖phi‖
  have hk0 := ProfileEnergy.gradientSquared_difference_tendsto_zero
    (B := max B Cfree) (u := fun n => M.state (seq n))
    (v := fun n => freeEnergyState hDensity hSob (seq n) phi)
    (fun n => (hseqCap n).trans (le_max_left B Cfree))
    (fun n => (freeEnergyState_norm_bound hDensity hSob (seq n) phi).trans (le_max_right B Cfree))
    (hasymptote.comp hseq)
  have hk : Tendsto (fun n => gradientSquared (M.state (seq n))) atTop (𝓝 (gradientSquared phi)) := by
    have hh := hk0.add_const (gradientSquared phi)
    simpa only [freeEnergyState_gradientSquared, sub_add_cancel, zero_add] using hh
  have hlim : Tendsto (fun n => totalEnergy alpha (M.state (seq n)))
      atTop (𝓝 (gradientSquared phi/2)) := by
    have hh := (hk.div_const 2).sub ((hpot.comp hseq).div_const (2*(3+alpha)))
    simpa only [totalEnergy, zero_div, sub_zero, Function.comp_def] using hh
  have hconst : ∀ t ∈ M.domain, totalEnergy alpha (M.state t) = totalEnergy alpha u0 := by
    intro t ht
    exact LocalMildTrajectory.totalEnergy_constant_on_domain hDensity hSob h0 hfree hret
      hefree heret hH S Bw Bs B6 M ht
  have hconstlim : Tendsto (fun n => totalEnergy alpha (M.state (seq n)))
      atTop (𝓝 (totalEnergy alpha u0)) := by
    have heq : (fun n => totalEnergy alpha (M.state (seq n))) =
        (fun _ : ℕ => totalEnergy alpha u0) := funext (fun n => hconst (seq n) (hseqDom n))
    rw [heq]
    exact tendsto_const_nhds
  have henergy : totalEnergy alpha u0 = gradientSquared phi/2 := tendsto_nhds_unique hconstlim hlim
  intro t ht
  exact (hconst t ht).trans henergy

end HartreeF.WaveRealization
