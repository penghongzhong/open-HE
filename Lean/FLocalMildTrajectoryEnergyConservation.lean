import FFiniteMildHartreeEnergyConservation
import FLocalMildTrajectory

/-!
This is the isolated implementation of the previously frozen preparation.
The old preparation and UNKNOWN record are preserved. Current acceptance is
reported by this directory's actual strict/dependency receipts.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.MaximalTrajectory.LocalMildTrajectory
open EnergySpace CriticalPathSpace IntervalTimeTransport StateEnergy
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain EndpointOutput
open Regularization.Actual
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue

/-- The actual LocalMildTrajectory supplies both its compact mild path and
that same path's full-Z endpoint witness. Neither is a new hypothesis. -/
theorem totalEnergy_compact_endpoints (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha s0 : ℝ} {u0 : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (U : LocalMildTrajectory alpha (HeatRiesz.standardRieszConstant alpha) s0 u0)
    {a b : ℝ} (hab : a ≤ b) (hI : Set.Icc a b ⊆ U.domain) :
    totalEnergy alpha (U.state b) = totalEnergy alpha (U.state a) := by
  obtain ⟨W⟩ := path_fullZ hDensity hSob h0 hfree hret hefree heret hH U hab hI
  have hE := actual_mild_energy_endpoints_withEndpoint hDensity hSob S hH hab Bw Bs B6
    (U.state a) (U.path hab hI) (U.path_mild hab hI) W
  have ha : energyPath _ (U.path hab hI) ⟨a, le_rfl, hab⟩ = U.state a :=
    U.path_agrees hab hI ⟨a, le_rfl, hab⟩
  have hb : energyPath _ (U.path hab hI) ⟨b, hab, le_rfl⟩ = U.state b :=
    U.path_agrees hab hI ⟨b, hab, le_rfl⟩
  rw [ha, hb] at hE
  exact hE

/-- Energy is constant on both time directions of the actual trajectory's
open connected domain. The only state datum is the homogeneous EnergyState. -/
theorem totalEnergy_constant_on_domain (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha s0 : ℝ} {u0 : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (U : LocalMildTrajectory alpha (HeatRiesz.standardRieszConstant alpha) s0 u0)
    {t : ℝ} (ht : t ∈ U.domain) : totalEnergy alpha (U.state t) = totalEnergy alpha u0 := by
  rcases le_total s0 t with hst | hts
  · have hI : Set.Icc s0 t ⊆ U.domain := U.domain_connected.out' U.center_mem ht
    have hE := totalEnergy_compact_endpoints hDensity hSob h0 hfree hret hefree heret hH
      S Bw Bs B6 U hst hI
    simpa only [U.initial] using hE
  · have hI : Set.Icc t s0 ⊆ U.domain := U.domain_connected.out' ht U.center_mem
    have hE := totalEnergy_compact_endpoints hDensity hSob h0 hfree hret hefree heret hH
      S Bw Bs B6 U hts hI
    simpa only [U.initial] using hE.symm

theorem totalEnergy_eqOn_initial (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha s0 : ℝ} {u0 : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (U : LocalMildTrajectory alpha (HeatRiesz.standardRieszConstant alpha) s0 u0) :
    Set.EqOn (fun t => totalEnergy alpha (U.state t))
      (fun _ => totalEnergy alpha u0) U.domain := by
  intro t ht
  exact totalEnergy_constant_on_domain hDensity hSob h0 hfree hret hefree heret hH
    S Bw Bs B6 U ht

/-- The same statement in the literal kinetic/interaction energy notation
of the paper, with the standard Riesz normalization and p=3+alpha. -/
theorem originalEnergy_constant_on_domain (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha s0 : ℝ} {u0 : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (U : LocalMildTrajectory alpha (HeatRiesz.standardRieszConstant alpha) s0 u0)
    {t : ℝ} (ht : t ∈ U.domain) :
    DirectionalCoercivity.energy alpha (energyValue (U.state t))
      (energyProjectedGradient Complex.reCLM (U.state t))
      (energyProjectedGradient Complex.imCLM (U.state t)) =
    DirectionalCoercivity.energy alpha (energyValue u0)
      (energyProjectedGradient Complex.reCLM u0)
      (energyProjectedGradient Complex.imCLM u0) := by
  simpa only [totalEnergy_eq_original] using
    totalEnergy_constant_on_domain hDensity hSob h0 hfree hret hefree heret hH S Bw Bs B6 U ht

#print axioms totalEnergy_compact_endpoints
#print axioms totalEnergy_constant_on_domain
#print axioms totalEnergy_eqOn_initial
#print axioms originalEnergy_constant_on_domain
end HartreeF.MaximalTrajectory.LocalMildTrajectory
