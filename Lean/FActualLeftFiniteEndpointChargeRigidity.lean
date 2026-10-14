import FActualLeftFiniteEndpointMassBound

/-!
Second reverse finite-interval estimate for the original Hartree charge. The L2
realization is made separately at each time, with no time-continuity claim.
This is the conditional native charge consumer, not a maximal-trajectory
left-finite-endpoint theorem: the local-charge endpoint limit remains explicit.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff
namespace HartreeF.ActualFiniteEndpointCharge
open EnergySpace LocalChargeBridge LocalDualSource LocalChargeRigidity
open ForcingDomain SobolevStretch StationarySelfTest CompactPDEDualBridge
open CutoffApproximation FiniteEndpointCalculus
attribute [local instance] energyRealSpace energyDualComplexNorm energyDualRealNorm
  energyDualComplexSpace energyDualRealSpace

/-- The second original-charge estimate: the bound tends to zero with the
exhausting cutoff radius, while the finite endpoint is held fixed. -/
theorem original_charge_le_left_finite_endpoint_decay
    (hD : OrdinaryH1Density) {K α c B T : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hord : OrdConnected S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    (hT : T ∈ closure S) (hafter : ∀ t ∈ S, T < t)
    (hcap : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    (hzero : ∀ n : ℕ, Tendsto
      (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (u t))) (𝓝[S] T) (𝓝 0))
    (n : ℕ) {a : ℝ} (ha : a ∈ S) :
    spatialCharge ((n : ℝ) + 1) (energyValue (u a)) ≤
      ((2 * baseGradientBound / ((n : ℝ) + 1)) *
        Real.sqrt (finiteChargeSlope K B * (a - T)) * B) * (a - T) := by
  apply (le_abs_self _).trans
  apply abs_le_left_endpoint_of_hasDerivAt_bound hord hT ha (hafter a ha)
    (fun t ht => original_spatialCharge_derivative_flux hD hSob
      (by positivity : 0 < (n : ℝ) + 1) hH hS hu hp ht) _ (hzero n)
  intro t ht hta
  obtain ⟨hm, hmass⟩ := original_memLp_two_and_left_mass_bound hD hSob hH hS hord hu hp
    hT hafter hcap hzero ht
  have hmass_a : (∫ x : V, ‖energyValue (u t) x‖ ^ 2) ≤
      finiteChargeSlope K B * (a - T) :=
    hmass.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hta T)
      (finiteChargeSlope_nonneg hSob B))
  exact (originalFlux_le_recovered_mass (by positivity : 0 < (n : ℝ) + 1)
    (u t) hm hmass_a).trans (mul_le_mul_of_nonneg_left (hcap t ht)
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) baseGradientBound_nonneg)
        (by positivity)) (Real.sqrt_nonneg _)))

/-- Exhausting original charges recover the original full mass, which is zero.
The recovered L2 domain is supplied before invoking dominated convergence. -/
theorem original_mass_eq_zero_of_left_finite_endpoint_charge_limit
    (hD : OrdinaryH1Density) {K α c B T : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hord : OrdConnected S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    (hT : T ∈ closure S) (hafter : ∀ t ∈ S, T < t)
    (hcap : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    (hzero : ∀ n : ℕ, Tendsto
      (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (u t))) (𝓝[S] T) (𝓝 0))
    {a : ℝ} (ha : a ∈ S) : (∫ x : V, ‖energyValue (u a) x‖ ^ 2) = 0 := by
  have hm := (original_memLp_two_and_left_mass_bound hD hSob hH hS hord hu hp
    hT hafter hcap hzero ha).1
  have hcut : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hleft := (spatialCharge_tendsto_mass hm).comp hcut
  have hright : Tendsto (fun n : ℕ =>
      ((2 * baseGradientBound / ((n : ℝ) + 1)) *
        Real.sqrt (finiteChargeSlope K B * (a - T)) * B) * (a - T)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (((hcut.const_div_atTop (2 * baseGradientBound)).mul_const
        (Real.sqrt (finiteChargeSlope K B * (a - T)))).mul_const B).mul_const (a - T)
  have hnonpos : (∫ x : V, ‖energyValue (u a) x‖ ^ 2) ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun n =>
      original_charge_le_left_finite_endpoint_decay hD hSob hH hS hord hu hp
        hT hafter hcap hzero n ha))
  exact le_antisymm hnonpos (integral_nonneg (fun x => sq_nonneg _))

/-- Conditional native left-finite-endpoint rigidity for the actual EnergyState
path. The explicit local-charge limits must still be produced from compact
normalized dynamics before applying this to a maximal original solution. -/
theorem original_zero_of_left_finite_endpoint_charge_limit
    (hD : OrdinaryH1Density) {K α c B T : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hord : OrdConnected S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    (hT : T ∈ closure S) (hafter : ∀ t ∈ S, T < t)
    (hcap : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    (hzero : ∀ n : ℕ, Tendsto
      (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (u t))) (𝓝[S] T) (𝓝 0)) :
    ∀ a ∈ S, u a = 0 := by
  intro a ha
  have hm := (original_memLp_two_and_left_mass_bound hD hSob hH hS hord hu hp
    hT hafter hcap hzero ha).1
  have hmass := original_mass_eq_zero_of_left_finite_endpoint_charge_limit hD hSob hH
    hS hord hu hp hT hafter hcap hzero ha
  have hae : (fun x : V => ‖energyValue (u a) x‖ ^ 2) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (hm.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))).mp hmass
  apply energyValue_injective
  rw [map_zero]
  apply Lp.ext
  filter_upwards [hae, Lp.coeFn_zero ℂ 6 (volume : Measure V)] with x hx hz
  have hv : energyValue (u a) x = 0 := by
    simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] using hx
  exact hv.trans hz.symm

end HartreeF.ActualFiniteEndpointCharge
