import FActualMaximalMildEnergyConservation

/-! Literal terminal wrapper for Theorem 3.6 of the 121-page manuscript:
the actual homogeneous Hartree energy is real C1 on the energy space and is
constant on the complete actual maximal lifespan, without an L2 hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set
namespace HartreeF.Paper121Theorem36
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest Retarded ActualStrichartz
open EndpointOutput ForcingDomain Regularization.Actual MaximalTrajectory StateEnergy

/-- Full Theorem 3.6, including identification with the literal kinetic and
double-interaction normalization used in the manuscript. -/
theorem theorem36_actual_energy_conservation
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6) :
    ContDiff ℝ 1 (totalEnergy alpha) ∧
    (∀ f : EnergyState,
      totalEnergy alpha f =
        SobolevStretch.kinetic (energyProjectedGradient Complex.reCLM f)
          (energyProjectedGradient Complex.imCLM f) / 2 -
        DirectionalCoercivity.interaction alpha (energyValue f) /
          (2 * (3 + alpha))) ∧
    ∀ (s0 : ℝ) (u0 : EnergyState),
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret
        hefree heret hH s0 u0
      ∀ t ∈ M.domain, totalEnergy alpha (M.state t) = totalEnergy alpha u0 := by
  refine ⟨totalEnergy_contDiff hH, fun f ↦ totalEnergy_eq_literal alpha f, ?_⟩
  intro s0 u0
  exact actualMaximalTrajectory_totalEnergy_constant hDensity hSob h0 hfree hret
    hefree heret hH S Bw Bs B6 s0 u0

end HartreeF.Paper121Theorem36
