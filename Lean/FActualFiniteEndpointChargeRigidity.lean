import FActualFiniteEndpointMassBound
import FEnergySchwartzDensity

/-!
Second finite-interval estimate for the original Hartree charge. The L2
realization is made separately at each time, with no time-continuity claim.
This is the conditional native charge consumer, not a maximal-trajectory
finite-endpoint theorem: the local-charge endpoint limit remains explicit.
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

/-- A single-time L2 realization of the original value allows the already
proved inverse-radius flux estimate. No L2 path or new flux axiom is used. -/
theorem originalFlux_le_recovered_mass {R M : ℝ} (hR : 0 < R) (u : EnergyState)
    (hm : MemLp (energyValue u : V → ℂ) 2 volume)
    (hM : (∫ x : V, ‖energyValue u x‖ ^ 2) ≤ M) :
    |2 * ∑ j : Fin 3, (∫ x : V, fluxIntegrand (χ := chargeCutoff R) u j x).im| ≤
      (2 * baseGradientBound / R) * Real.sqrt M * pureGradientNorm u := by
  let v : L2 := hm.toLp (energyValue u)
  have hae : (v : V → ℂ) =ᵐ[volume] energyValue u := MemLp.coeFn_toLp hm
  have hvnorm : ‖v‖ ≤ Real.sqrt M := by
    apply Real.le_sqrt_of_sq_le
    change ‖hm.toLp (energyValue u)‖ ^ 2 ≤ M
    rw [Lp.norm_toLp]
    exact (ComplexIMS.integral_norm_sq_eq_eLpNorm_sq hm).symm.le.trans hM
  calc
    _ = 2 * |∑ j : Fin 3,
        (∫ x : V, fluxIntegrand (χ := chargeCutoff R) u j x).im| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ((baseGradientBound / R) * ‖v‖ * pureGradientNorm u) :=
      mul_le_mul_of_nonneg_left (originalFlux_exact_bound hR u v hae) (by norm_num)
    _ ≤ 2 * ((baseGradientBound / R) * Real.sqrt M * pureGradientNorm u) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_right _ (pureGradientNorm_nonneg u)
      exact mul_le_mul_of_nonneg_left hvnorm (div_nonneg baseGradientBound_nonneg hR.le)
    _ = _ := by ring

/-- The second original-charge estimate: the bound tends to zero with the
exhausting cutoff radius, while the finite endpoint is held fixed. -/
theorem original_charge_le_finite_endpoint_decay
    (hD : OrdinaryH1Density) {K α c B T : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hord : OrdConnected S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    (hT : T ∈ closure S) (hbefore : ∀ t ∈ S, t < T)
    (hcap : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    (hzero : ∀ n : ℕ, Tendsto
      (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (u t))) (𝓝[S] T) (𝓝 0))
    (n : ℕ) {a : ℝ} (ha : a ∈ S) :
    spatialCharge ((n : ℝ) + 1) (energyValue (u a)) ≤
      ((2 * baseGradientBound / ((n : ℝ) + 1)) *
        Real.sqrt (finiteChargeSlope K B * (T - a)) * B) * (T - a) := by
  apply (le_abs_self _).trans
  apply abs_le_endpoint_of_hasDerivAt_bound hord hT ha (hbefore a ha)
    (fun t ht => original_spatialCharge_derivative_flux hD hSob
      (by positivity : 0 < (n : ℝ) + 1) hH hS hu hp ht) _ (hzero n)
  intro t ht hat
  obtain ⟨hm, hmass⟩ := original_memLp_two_and_mass_bound hD hSob hH hS hord hu hp
    hT hbefore hcap hzero ht
  have hmass_a : (∫ x : V, ‖energyValue (u t) x‖ ^ 2) ≤
      finiteChargeSlope K B * (T - a) :=
    hmass.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hat T)
      (finiteChargeSlope_nonneg hSob B))
  exact (originalFlux_le_recovered_mass (by positivity : 0 < (n : ℝ) + 1)
    (u t) hm hmass_a).trans (mul_le_mul_of_nonneg_left (hcap t ht)
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) baseGradientBound_nonneg)
        (by positivity)) (Real.sqrt_nonneg _)))

/-- Exhausting original charges recover the original full mass, which is zero.
The recovered L2 domain is supplied before invoking dominated convergence. -/
theorem original_mass_eq_zero_of_finite_endpoint_charge_limit
    (hD : OrdinaryH1Density) {K α c B T : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hord : OrdConnected S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    (hT : T ∈ closure S) (hbefore : ∀ t ∈ S, t < T)
    (hcap : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    (hzero : ∀ n : ℕ, Tendsto
      (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (u t))) (𝓝[S] T) (𝓝 0))
    {a : ℝ} (ha : a ∈ S) : (∫ x : V, ‖energyValue (u a) x‖ ^ 2) = 0 := by
  have hm := (original_memLp_two_and_mass_bound hD hSob hH hS hord hu hp
    hT hbefore hcap hzero ha).1
  have hcut : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hleft := (spatialCharge_tendsto_mass hm).comp hcut
  have hright : Tendsto (fun n : ℕ =>
      ((2 * baseGradientBound / ((n : ℝ) + 1)) *
        Real.sqrt (finiteChargeSlope K B * (T - a)) * B) * (T - a)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (((hcut.const_div_atTop (2 * baseGradientBound)).mul_const
        (Real.sqrt (finiteChargeSlope K B * (T - a)))).mul_const B).mul_const (T - a)
  have hnonpos : (∫ x : V, ‖energyValue (u a) x‖ ^ 2) ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun n =>
      original_charge_le_finite_endpoint_decay hD hSob hH hS hord hu hp
        hT hbefore hcap hzero n ha))
  exact le_antisymm hnonpos (integral_nonneg (fun x => sq_nonneg _))

/-- Conditional native finite-endpoint rigidity for the actual EnergyState
path. The explicit local-charge limits must still be produced from compact
normalized dynamics before applying this to a maximal original solution. -/
theorem original_zero_of_finite_endpoint_charge_limit
    (hD : OrdinaryH1Density) {K α c B T : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hord : OrdConnected S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S)
    (hT : T ∈ closure S) (hbefore : ∀ t ∈ S, t < T)
    (hcap : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    (hzero : ∀ n : ℕ, Tendsto
      (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (u t))) (𝓝[S] T) (𝓝 0)) :
    ∀ a ∈ S, u a = 0 := by
  intro a ha
  have hm := (original_memLp_two_and_mass_bound hD hSob hH hS hord hu hp
    hT hbefore hcap hzero ha).1
  have hmass := original_mass_eq_zero_of_finite_endpoint_charge_limit hD hSob hH
    hS hord hu hp hT hbefore hcap hzero ha
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
