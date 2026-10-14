import FActualRegularizedEnergyResidual
import FVanishingActualEnergyIntegral
import FStateEnergyConsumers
import FHartreeSubintervalFixedPoint

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
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace IntervalTimeTransport ForcingDomain ForcingContinuity
open EndpointOutput StateEnergy CriticalUniqueness ActualDuhamelPath
open Retarded ActualStrichartz CriticalPathRestriction
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue
  hartreeDuhamelMap restrictPath actualRegularizedEnergyError

/-- Endpoint passage with an explicit actual endpoint witness. The energy
increment limit is produced from the actual mild identity and the proven
vanishing actual error integral, never supplied as a hypothesis. -/
theorem actual_mild_energy_endpoints_withEndpoint (hDensity : OrdinaryH1Density)
    {K alpha a b : ℝ} (hSob : OrdinarySobolev K) (S : OrdinaryBesselSmoothing)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hab : a ≤ b) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha (HeatRiesz.standardRieszConstant alpha) u0 u)
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ u)) :
    totalEnergy alpha (energyPath _ u ⟨b, hab, le_rfl⟩) =
      totalEnergy alpha (energyPath _ u ⟨a, le_rfl, hab⟩) := by
  let v := extendEnergyPath hab (energyPath _ u)
  have herr := actualRegularizedEnergyError_integral_tendsto_zero
    hDensity hSob hH hab Bw Bs B6 u W
  have hinc : Tendsto (fun n => totalEnergy alpha (J hDensity hSob n (v b)) -
      totalEnergy alpha (J hDensity hSob n (v a))) atTop (𝓝 0) :=
    Tendsto.congr' (Eventually.of_forall (fun n =>
      (actual_mild_energy_error_increment hDensity hSob S hH hab Bw Bs u0 u hmild n).symm)) herr
  have hE : totalEnergy alpha (v b) = totalEnergy alpha (v a) :=
    totalEnergy_endpoint_limit hH
      (u := fun n t => J hDensity hSob n (v t)) (v := v) (a := a) (b := b)
      (J_strong hDensity hSob (v a)) (J_strong hDensity hSob (v b)) hinc
  have ha : v a = energyPath _ u ⟨a, le_rfl, hab⟩ :=
    extendEnergyPath_val hab (energyPath _ u) ⟨a, le_rfl, hab⟩
  have hb : v b = energyPath _ u ⟨b, hab, le_rfl⟩ :=
    extendEnergyPath_val hab (energyPath _ u) ⟨b, hab, le_rfl⟩
  rw [ha, hb] at hE
  exact hE

/-- The endpoint witness is produced by fixedPoint_fullZ from the literal
mild equation. Only the existing eight ordinary analytic hypotheses and
the stated ordinary Bessel interfaces occur in this final finite-path root. -/
theorem actual_mild_energy_terminal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha (HeatRiesz.standardRieszConstant alpha) u0 u) :
    totalEnergy alpha (energyPath _ u ⟨b, hab, le_rfl⟩) = totalEnergy alpha u0 := by
  have hfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab u0 u).mp hmild
  obtain ⟨W⟩ := fixedPoint_fullZ hDensity hSob h0 hfree hret hefree heret hH hab u0 u hfix
  have hE := actual_mild_energy_endpoints_withEndpoint hDensity hSob S hH hab Bw Bs B6 u0 u hmild W
  have hinit : energyPath _ u ⟨a, le_rfl, hab⟩ = u0 := by
    have hi := hartreeDuhamelMap_initial hDensity hSob h0 hfree hret hH hab u0 u
    exact (congrArg (fun w : CriticalPath (intervalMeasure a b) =>
      energyPath _ w ⟨a, le_rfl, hab⟩) hfix).symm.trans hi
  exact hE.trans (congrArg (totalEnergy alpha) hinit)

/-- Every time of the actual finite mild path has the initial paper energy.
The subinterval mild equation and its full-Z witness are both produced from
the accepted restriction and endpoint constructions. -/
theorem actual_mild_energy_constant (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hab : a ≤ b) (u0 : EnergyState) (u : CriticalPath (intervalMeasure a b))
    (hmild : IsMildHartreePath hab alpha (HeatRiesz.standardRieszConstant alpha) u0 u)
    (t : Set.Icc a b) : totalEnergy alpha (energyPath _ u t) = totalEnergy alpha u0 := by
  have hfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab u0 u).mp hmild
  let v := restrictPath (a := a) (b := b) (c := a) (d := (t : ℝ)) le_rfl t.property.1 t.property.2 u
  have hvfix := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    (a := a) (b := b) (c := a) (d := (t : ℝ)) le_rfl t.property.1 t.property.2 u0 u
    (by exact hfix)
  have hvmild : IsMildHartreePath t.property.1 alpha (HeatRiesz.standardRieszConstant alpha)
      (energyPath _ u ⟨a, le_rfl, hab⟩) v :=
    (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH t.property.1
      (energyPath _ u ⟨a, le_rfl, hab⟩) v).mpr hvfix
  have hE := actual_mild_energy_terminal hDensity hSob h0 hfree hret hefree heret hH
    S Bw Bs B6 t.property.1 (energyPath _ u ⟨a, le_rfl, hab⟩) v hvmild
  have hvend : energyPath _ v ⟨(t : ℝ), t.property.1, le_rfl⟩ = energyPath _ u t := by
    exact restrictPath_energy le_rfl t.property.1 t.property.2 u ⟨(t : ℝ), t.property.1, le_rfl⟩
  have hinit : energyPath _ u ⟨a, le_rfl, hab⟩ = u0 := by
    have hi := hartreeDuhamelMap_initial hDensity hSob h0 hfree hret hH hab u0 u
    exact (congrArg (fun w : CriticalPath (intervalMeasure a b) =>
      energyPath _ w ⟨a, le_rfl, hab⟩) hfix).symm.trans hi
  exact (congrArg (totalEnergy alpha) hvend).symm.trans
    (hE.trans (congrArg (totalEnergy alpha) hinit))

#print axioms actual_mild_energy_endpoints_withEndpoint
#print axioms actual_mild_energy_terminal
#print axioms actual_mild_energy_constant
end HartreeF.Regularization.Actual
