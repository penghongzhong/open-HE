import FRetardedEnergyContinuity
import FRetardedTransport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Retarded
open FreeFlow EnergySpace SobolevStretch StationarySelfTest

/-- Splitting the literal retarded scalar integral uses the actual integrability
part of the retained endpoint estimate. No totalized nonintegrable splitting is used. -/
theorem scalarIntegrand_forward_split {C : ℝ} (h : OrdinaryEndpointBound C)
    {a r t : ℝ} (har : a ≤ r) (hrt : r ≤ t) (F : EndpointSource) (φ : FreeFlow.Test) :
    (∫ s in Set.Ioc a t, scalarIntegrand t F φ s) =
      (∫ s in Set.Ioc a r, scalarIntegrand t F φ s) +
      ∫ s in Set.Ioc r t, scalarIntegrand t F φ s := by
  rw [← Set.Ioc_union_Ioc_eq_Ioc har hrt]
  exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (h.2 _ measurableSet_Ioc t F φ).1 (h.2 _ measurableSet_Ioc t F φ).1

/-- The actual L2 retarded realization has the exact restart identity. -/
theorem forwardL2_restart {C : ℝ} (h : OrdinaryEndpointBound C)
    {a r t : ℝ} (har : a ≤ r) (hrt : r ≤ t) (F : EndpointSource) :
    forwardL2 h a F t = freeL2 (t-r) (forwardL2 h a F r) + forwardL2 h r F t := by
  apply l2_distribution_injective
  ext φ
  change _ = (Lp.toTemperedDistributionCLM ℂ (volume : Measure FreeFlow.V) 2
    (freeL2 (t-r) (forwardL2 h a F r) + forwardL2 h r F t)) φ
  rw [map_add]
  change _ = Lp.toTemperedDistribution (freeL2 (t-r) (forwardL2 h a F r)) φ +
    Lp.toTemperedDistribution (forwardL2 h r F t) φ
  rw [freeL2_distribution, free_apply,
    forwardL2_scalar, forwardL2_scalar, forwardL2_scalar]
  rw [scalarIntegrand_forward_split h har hrt]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by
    simpa only [sub_add_cancel] using (scalarIntegrand_transport (t-r) r s F φ).symm)

/-- Compatible endpoint sources produce the restart identity in the complete
energy space; the output gradient compatibility is not an input. -/
theorem forwardEnergyState_restart (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) =
        Lp.toTemperedDistribution (G j s))
    {a r t : ℝ} (har : a ≤ r) (hrt : r ≤ t) :
    forwardEnergyState hDensity hSob h a F G hFG t =
      freeEnergyState hDensity hSob (t-r)
        (forwardEnergyState hDensity hSob h a F G hFG r) +
      forwardEnergyState hDensity hSob h r F G hFG t := by
  apply energyDistribution_injective
  ext φ
  rw [map_add, add_apply, freeEnergyState_distribution, free_apply,
    forwardEnergyState_scalar, forwardEnergyState_scalar, forwardEnergyState_scalar]
  rw [scalarIntegrand_forward_split h har hrt]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun s => by
    simpa only [sub_add_cancel] using (scalarIntegrand_transport (t-r) r s F φ).symm)

/-- Restart of the same inhomogeneous energy trajectory, with the focusing
Schrodinger coefficient +i and without an L2 condition on the initial datum. -/
theorem inhomogeneousEnergy_restart (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) =
        Lp.toTemperedDistribution (G j s))
    {a r t : ℝ} (har : a ≤ r) (hrt : r ≤ t) (u0 : EnergyState) :
    freeEnergyState hDensity hSob (t-a) u0 +
        Complex.I • forwardEnergyState hDensity hSob h a F G hFG t =
      freeEnergyState hDensity hSob (t-r)
        (freeEnergyState hDensity hSob (r-a) u0 +
          Complex.I • forwardEnergyState hDensity hSob h a F G hFG r) +
        Complex.I • forwardEnergyState hDensity hSob h r F G hFG t := by
  rw [forwardEnergyState_restart hDensity hSob h F G hFG har hrt,
    freeEnergyState_add, freeEnergyState_smul, ← freeEnergyState_add_time,
    smul_add]
  have ht : t-r+(r-a)=t-a := by ring
  rw [ht]
  abel

end HartreeF.Retarded
