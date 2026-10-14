import FNativeCompactScaleCollapse
import FCompactLocalMassNative
import FActualFiniteEndpointChargeRigidity
import FActualLeftFiniteEndpointChargeRigidity
import FLocalMildTrajectoryToDomainPDE

/-! Actual finite-endpoint exclusion for a compactly normalized canonical
maximal Hartree trajectory, following the existing R8.4 crit:global proof.
AUTHOR CANDIDATE, NOT COMPILED. The final theorem assumes neither its PDE,
charge endpoint limits, uniform lifespan nor scale collapse: each is produced.
It retains the project's explicitly named ordinary analytic interfaces. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace HartreeF.NativeCompactGlobal
open EnergySpace SobolevStretch StationarySelfTest Retarded ActualStrichartz
open EndpointOutput ForcingDomain MaximalTrajectory CriticalAffine
open LocalChargeBridge LocalChargeRigidity CompactLocalMass NativeCompactScale
open ActualFiniteEndpointCharge LinearWeakEquation HartreeMildPDEProducer

/-- Compactness controls the actual homogeneous gradient norm. Positivity and
normalized-carrier membership are required only inside the original domain. -/
theorem compact_normalized_gradient_bound {Q : Set EnergyState} (hQ : IsCompact Q)
    {S : Set ℝ} (u : ℝ → EnergyState) (ρ : ℝ → ℝ) (y : ℝ → Space)
    (hρ : ∀ t ∈ S, 0 < ρ t)
    (hq : ∀ t (ht : t ∈ S), (criticalAffineState (ρ t) (hρ t ht) (y t)).symm (u t) ∈ Q) :
    ∃ B : ℝ, ∀ t ∈ S, pureGradientNorm (u t) ≤ B := by
  obtain ⟨C, _hCpos, hC⟩ := hQ.isBounded.exists_pos_norm_le
  refine ⟨Real.sqrt 3 * C, ?_⟩
  intro t ht
  have hn := hC _ (hq t ht)
  rw [(criticalAffineState (ρ t) (hρ t ht) (y t)).symm.norm_map] at hn
  exact (pureGradient_le_sqrt_three_energyState (u t)).trans
    (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg 3))

/-- Local charge decay is produced from the actual normalized states on S.
There is no positivity, compactness, regularity or measurability premise on
any arbitrary outside-domain fill of the normalization parameters. -/
theorem original_charge_tendsto_zero_of_compact_collapse
    (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    {Q : Set EnergyState} (hQ : IsCompact Q) {S : Set ℝ} {T R : ℝ}
    (hR : 0 < R) (u : ℝ → EnergyState) (ρ : ℝ → ℝ) (y : ℝ → Space)
    (hρ : ∀ t ∈ S, 0 < ρ t)
    (hq : ∀ t (ht : t ∈ S), (criticalAffineState (ρ t) (hρ t ht) (y t)).symm (u t) ∈ Q)
    (hc : Tendsto ρ (𝓝[S] T) (𝓝 0)) :
    Tendsto (fun t => spatialCharge R (energyValue (u t))) (𝓝[S] T) (𝓝 0) := by
  have hv : Tendsto (fun t => physicalChargeValue hR (u t)) (𝓝[S] T) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := compact_physicalChargeValue_small hD hS hQ hR hε
    filter_upwards [self_mem_nhdsWithin, hc.eventually_lt_const hδ] with t ht hlt
    have hs := hsmall (ρ t) (hρ t ht) hlt (y t)
      ((criticalAffineState (ρ t) (hρ t ht) (y t)).symm (u t)) (hq t ht)
    rw [(criticalAffineState (ρ t) (hρ t ht) (y t)).apply_symm_apply] at hs
    simpa only [dist_zero_right] using hs
  simp_rw [CompactLocalMass.spatialCharge_eq_norm_sq hR]
  simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hv.norm.pow 2

/-- Every member of an open real set is strictly below its finite supremum. -/
theorem open_mem_lt_csSup {S : Set ℝ} (hS : IsOpen S) (hb : BddAbove S)
    {t : ℝ} (ht : t ∈ S) : t < sSup S := by
  obtain ⟨a, b, htI, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds ht)
  obtain ⟨z, htz, hzb⟩ := exists_between htI.2
  exact htz.trans_le (le_csSup hb (hI ⟨htI.1.trans htz, hzb⟩))

/-- Every member of an open real set is strictly above its finite infimum. -/
theorem open_csInf_lt_mem {S : Set ℝ} (hS : IsOpen S) (hb : BddBelow S)
    {t : ℝ} (ht : t ∈ S) : sInf S < t := by
  obtain ⟨a, b, htI, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds ht)
  obtain ⟨z, haz, hzt⟩ := exists_between htI.1
  exact (csInf_le hb (hI ⟨haz, hzt.trans htI.2⟩)).trans_lt hzt

/-- Both finite endpoint alternatives contradict the SAME nonzero original
datum. Actual PDE, gradient cap, common lifespan, collapse, local mass limits,
and the two finite-endpoint consumers are instantiated in this proof. -/
theorem actual_compact_normalized_domain_unbounded (hD : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s : ℝ}
    (hS : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (f : EnergyState) (hf : f ≠ 0) {Q : Set EnergyState} (hQ : IsCompact Q)
    (ρ : ℝ → ℝ) (y : ℝ → Space) :
    let M := actualMaximalTrajectory hD hS h0 hfree hret hefree heret hH s f
    ∀ hρ : ∀ t ∈ M.domain, 0 < ρ t,
      (∀ t (ht : t ∈ M.domain),
        (criticalAffineState (ρ t) (hρ t ht) (y t)).symm (M.state t) ∈ Q) →
      ¬ BddAbove M.domain ∧ ¬ BddBelow M.domain := by
  intro M hρ hq
  obtain ⟨B, hcap⟩ := compact_normalized_gradient_bound hQ M.state ρ y hρ hq
  obtain ⟨δ, hδ, hwindow⟩ := exists_actual_compact_normalized_window
    hD hS h0 hfree hret hefree heret hH hQ
  have hp := localMildTrajectory_domain_tensorPDE hD hS hH h0 hfree hret hgen M
  have hne : M.domain.Nonempty := ⟨s, M.center_mem⟩
  constructor
  · intro hb
    have hT : sSup M.domain ∈ closure M.domain := csSup_mem_closure hne hb
    have hbefore : ∀ t ∈ M.domain, t < sSup M.domain :=
      fun _ ht => open_mem_lt_csSup M.domain_open hb ht
    have hc : Tendsto ρ (𝓝[M.domain] (sSup M.domain)) (𝓝 0) := by
      apply scale_tendsto_zero_at_right_endpoint hδ hbefore ρ hρ
      intro t ht
      have hw := hwindow s f t ht (ρ t) (hρ t ht) (y t) (hq t ht)
        δ (show δ ∈ Icc (-δ) δ from ⟨by linarith, le_rfl⟩)
      simpa only [mul_comm] using hw
    have hz : ∀ n : ℕ, Tendsto
        (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (M.state t)))
        (𝓝[M.domain] (sSup M.domain)) (𝓝 0) := fun n =>
      original_charge_tendsto_zero_of_compact_collapse hD hS hQ
        (by positivity) M.state ρ y hρ hq hc
    have hzero := original_zero_of_finite_endpoint_charge_limit hD hS hH
      M.domain_open M.domain_connected M.continuous hp hT hbefore hcap hz s M.center_mem
    exact hf (M.initial.symm.trans hzero)
  · intro hb
    have hT : sInf M.domain ∈ closure M.domain := csInf_mem_closure hne hb
    have hafter : ∀ t ∈ M.domain, sInf M.domain < t :=
      fun _ ht => open_csInf_lt_mem M.domain_open hb ht
    have hc : Tendsto ρ (𝓝[M.domain] (sInf M.domain)) (𝓝 0) := by
      apply scale_tendsto_zero_at_left_endpoint hδ hafter ρ hρ
      intro t ht
      have hw := hwindow s f t ht (ρ t) (hρ t ht) (y t) (hq t ht)
        (-δ) (show -δ ∈ Icc (-δ) δ from ⟨le_rfl, by linarith⟩)
      convert hw using 1; ring
    have hz : ∀ n : ℕ, Tendsto
        (fun t => spatialCharge ((n : ℝ) + 1) (energyValue (M.state t)))
        (𝓝[M.domain] (sInf M.domain)) (𝓝 0) := fun n =>
      original_charge_tendsto_zero_of_compact_collapse hD hS hQ
        (by positivity) M.state ρ y hρ hq hc
    have hzero := original_zero_of_left_finite_endpoint_charge_limit hD hS hH
      M.domain_open M.domain_connected M.continuous hp hT hafter hcap hz s M.center_mem
    exact hf (M.initial.symm.trans hzero)

/-- The native formal counterpart of R8.4 Proposition crit:global. This proves
globality of a nonzero compactly normalized actual maximal trajectory. It does
not produce such a trajectory from a threshold counterexample or prove scattering. -/
theorem actual_compact_normalized_global (hD : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s : ℝ}
    (hS : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (f : EnergyState) (hf : f ≠ 0) {Q : Set EnergyState} (hQ : IsCompact Q)
    (ρ : ℝ → ℝ) (y : ℝ → Space) :
    let M := actualMaximalTrajectory hD hS h0 hfree hret hefree heret hH s f
    ∀ hρ : ∀ t ∈ M.domain, 0 < ρ t,
      (∀ t (ht : t ∈ M.domain),
        (criticalAffineState (ρ t) (hρ t ht) (y t)).symm (M.state t) ∈ Q) →
      M.domain = Set.univ := by
  intro M hρ hq
  obtain ⟨habove, hbelow⟩ := actual_compact_normalized_domain_unbounded
    hD hS h0 hfree hret hefree heret hH hgen f hf hQ ρ y hρ hq
  apply Set.eq_univ_iff_forall.mpr
  intro t
  obtain ⟨a, ha, hat⟩ := not_bddBelow_iff.mp hbelow t
  obtain ⟨b, hb, htb⟩ := not_bddAbove_iff.mp habove t
  exact M.domain_connected.out' ha hb ⟨hat.le, htb.le⟩

end HartreeF.NativeCompactGlobal
