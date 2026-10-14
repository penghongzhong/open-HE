import FCriticalAffineL2Continuity
import FActualQuadraticChargeRule
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
Native finite-endpoint compact local-mass bridge, implementing the existing
R8.4 compact-smooth finite-net argument. AUTHOR CANDIDATE; NOT COMPILED.
The original EnergyState values are never assumed to belong to L2.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace HartreeF.CompactLocalMass
open EnergySpace SobolevStretch StationarySelfTest CriticalAffine LocalChargeBridge LocalChargeRigidity

/-- The actual homogeneous compact carrier has a finite compact-smooth net. -/
theorem compact_smooth_finite_net (hD : OrdinaryH1Density)
    {K : ℝ} (hS : OrdinarySobolev K) {Q : Set EnergyState} (hQ : IsCompact Q)
    {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset (CompactSmoothReal × CompactSmoothReal),
      ∀ h ∈ Q, ∃ φ ∈ S, ‖h - compactSmoothState φ‖ < η := by
  classical
  have hdense := compactSmoothState_denseRange hD hS
  have happrox (a : EnergyState) :
      ∃ φ : CompactSmoothReal × CompactSmoothReal,
        ‖a - compactSmoothState φ‖ < η / 2 := by
    obtain ⟨g, ⟨φ, rfl⟩, hnear⟩ :=
      Metric.mem_closure_iff.mp (hdense a) (η / 2) (half_pos hη)
    exact ⟨φ, by simpa only [dist_eq_norm] using hnear⟩
  choose φ hφ using happrox
  obtain ⟨S, _hSQ, hSfin, hcover⟩ := hQ.finite_cover_balls (half_pos hη)
  refine ⟨hSfin.toFinset.image φ, ?_⟩
  intro h hh
  obtain ⟨a, ha, hha⟩ : ∃ a ∈ S, h ∈ ball a (η / 2) := by
    simpa only [mem_iUnion, exists_prop] using hcover hh
  refine ⟨φ a, Finset.mem_image.mpr ⟨a, hSfin.mem_toFinset.mpr ha, rfl⟩, ?_⟩
  have hnear : ‖h - a‖ < η / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hha
  calc
    ‖h - compactSmoothState (φ a)‖
        ≤ ‖h - a‖ + ‖a - compactSmoothState (φ a)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < η / 2 + η / 2 := add_lt_add hnear (hφ a)
    _ = η := add_halves η

/-- Only a genuine compact-smooth approximant receives a global L2 value. -/
def compactSmoothL2 (φ : CompactSmoothReal × CompactSmoothReal) : L2 :=
  ((compactSmoothFunction_contDiff φ).continuous.memLp_of_hasCompactSupport
    (compactSmoothFunction_support φ) (p := 2)).toLp (compactSmoothFunction φ)

theorem compactSmoothL2_ae (φ : CompactSmoothReal × CompactSmoothReal) :
    (compactSmoothL2 φ : Space → ℂ) =ᵐ[volume] compactSmoothFunction φ :=
  MemLp.coeFn_toLp _

/-- The physical value scaling is rho times the already proved L2 isometry.
This definition applies solely to compact-smooth approximants. -/
def criticalSmoothL2 (ρ : ℝ) (hρ : 0 < ρ) (y : Space)
    (φ : CompactSmoothReal × CompactSmoothReal) : L2 :=
  ρ • gradientAffineL2 (inv_pos.mpr hρ) (-(ρ⁻¹ • y)) (compactSmoothL2 φ)

theorem criticalSmoothL2_norm (ρ : ℝ) (hρ : 0 < ρ) (y : Space)
    (φ : CompactSmoothReal × CompactSmoothReal) :
    ‖criticalSmoothL2 ρ hρ y φ‖ = ρ * ‖compactSmoothL2 φ‖ := by
  rw [criticalSmoothL2, norm_smul, Real.norm_of_nonneg hρ.le, LinearIsometry.norm_map]

/-- The smooth L2 class represents exactly the same physical affine EnergyState. -/
theorem criticalSmoothL2_same_value (ρ : ℝ) (hρ : 0 < ρ) (y : Space)
    (φ : CompactSmoothReal × CompactSmoothReal) :
    (criticalSmoothL2 ρ hρ y φ : Space → ℂ) =ᵐ[volume]
      energyValue (criticalAffineState ρ hρ y (compactSmoothState φ)) := by
  let a : ℝ := ρ⁻¹
  let b : Space := -(ρ⁻¹ • y)
  have ha : 0 < a := inv_pos.mpr hρ
  have hv := (affine_quasiMeasurePreserving ha.ne' b).ae
    (compactSmoothState_value_ae φ)
  have hg := (affine_quasiMeasurePreserving ha.ne' b).ae (compactSmoothL2_ae φ)
  have hs := Lp.coeFn_smul ρ (gradientAffineL2 ha b (compactSmoothL2 φ))
  have hout := affineState_value_ae ha b (compactSmoothState φ)
  filter_upwards [hs, gradientAffineL2_ae ha b (compactSmoothL2 φ), hg, hv, hout]
    with x hs hg hx hv hout
  change criticalSmoothL2 ρ hρ y φ x = energyValue (affineState ha b (compactSmoothState φ)) x
  change (ρ • gradientAffineL2 ha b (compactSmoothL2 φ)) x = _
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hg, hout]
  simp only [gradientPullback, valuePullback, hx, hv, smul_smul]
  congr 1
  dsimp [a]
  rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]

/-- The real compact coefficient defines a genuine continuous linear local L2 value. -/
def compactLocalValue {χ : Space → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) : EnergyState →L[ℂ] L2 :=
  (cutoffL6L2 hχ hc).comp energyValue

/-- Localization of the smooth physical state is exactly localization of its L2 class. -/
theorem compactLocalValue_smooth_eq {χ : Space → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (ρ : ℝ) (hρ : 0 < ρ) (y : Space)
    (φ : CompactSmoothReal × CompactSmoothReal) :
    compactLocalValue hχ hc (criticalAffineState ρ hρ y (compactSmoothState φ)) =
      cutoffL2L2 hχ hc (criticalSmoothL2 ρ hρ y φ) := by
  apply Lp.ext
  filter_upwards [cutoffL6L2_ae hχ hc
      (energyValue (criticalAffineState ρ hρ y (compactSmoothState φ))),
    cutoffL2L2_ae hχ hc (criticalSmoothL2 ρ hρ y φ),
    criticalSmoothL2_same_value ρ hρ y φ] with x hx hy he
  change compactLocalValue hχ hc (criticalAffineState ρ hρ y (compactSmoothState φ)) x = _ at hx
  rw [hx, hy, he]

/-- The smooth term is O(rho), uniformly over every translation center. -/
theorem compactLocalValue_smooth_norm_le {χ : Space → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (ρ : ℝ) (hρ : 0 < ρ) (y : Space)
    (φ : CompactSmoothReal × CompactSmoothReal) :
    ‖compactLocalValue hχ hc (criticalAffineState ρ hρ y (compactSmoothState φ))‖ ≤
      ρ * (‖coefficientLp hχ hc ∞‖ * ‖compactSmoothL2 φ‖) := by
  rw [compactLocalValue_smooth_eq]
  calc
    _ ≤ ‖coefficientLp hχ hc ∞‖ * ‖criticalSmoothL2 ρ hρ y φ‖ :=
      cutoffL2L2_norm hχ hc _
    _ = _ := by rw [criticalSmoothL2_norm]; ring

/-- Affine isometry controls the error in the original homogeneous EnergyState norm. -/
theorem compactLocalValue_affine_sub_norm_le {χ : Space → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (ρ : ℝ) (hρ : 0 < ρ) (y : Space)
    (h g : EnergyState) :
    ‖compactLocalValue hχ hc (criticalAffineState ρ hρ y h) -
      compactLocalValue hχ hc (criticalAffineState ρ hρ y g)‖ ≤
      ‖compactLocalValue hχ hc‖ * ‖h - g‖ := by
  rw [← map_sub, ← map_sub]
  exact ((compactLocalValue hχ hc).le_opNorm _).trans_eq
    (congrArg (fun z : ℝ => ‖compactLocalValue hχ hc‖ * z)
      ((criticalAffineState ρ hρ y).norm_map (h - g)))

/-- The finite-net estimate, with all centers unrestricted and only smooth L2 norms.
The finite sum bounds the manuscript's finite maximum, including an empty carrier. -/
theorem compact_localValue_finite_net_bound (hD : OrdinaryH1Density)
    {K : ℝ} (hS : OrdinarySobolev K) {Q : Set EnergyState} (hQ : IsCompact Q)
    {χ : Space → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {η : ℝ} (hη : 0 < η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ) (y : Space) (h : EnergyState),
      h ∈ Q → ‖compactLocalValue hχ hc (criticalAffineState ρ hρ y h)‖ ≤
        ‖compactLocalValue hχ hc‖ * η + ρ * L := by
  classical
  obtain ⟨S, hnet⟩ := compact_smooth_finite_net hD hS hQ hη
  let L : ℝ := ∑ φ ∈ S, ‖coefficientLp hχ hc ∞‖ * ‖compactSmoothL2 φ‖
  have hL : 0 ≤ L := Finset.sum_nonneg fun φ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine ⟨L, hL, ?_⟩
  intro ρ hρ y h hh
  obtain ⟨φ, hφ, hnear⟩ := hnet h hh
  have hsingle : ‖coefficientLp hχ hc ∞‖ * ‖compactSmoothL2 φ‖ ≤ L :=
    Finset.single_le_sum (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hφ
  have herr := compactLocalValue_affine_sub_norm_le hχ hc ρ hρ y h (compactSmoothState φ)
  have hsmooth := compactLocalValue_smooth_norm_le hχ hc ρ hρ y φ
  calc
    _ ≤ ‖compactLocalValue hχ hc (criticalAffineState ρ hρ y h) -
          compactLocalValue hχ hc (criticalAffineState ρ hρ y (compactSmoothState φ))‖ +
        ‖compactLocalValue hχ hc (criticalAffineState ρ hρ y (compactSmoothState φ))‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ ‖compactLocalValue hχ hc‖ * η + ρ * L :=
      add_le_add
        (herr.trans (mul_le_mul_of_nonneg_left hnear.le
          (ContinuousLinearMap.opNorm_nonneg (compactLocalValue hχ hc))))
        (hsmooth.trans (mul_le_mul_of_nonneg_left hsingle hρ.le))

/-- The manuscript's epsilon-squared plus rho-squared estimate on the actual compact carrier. -/
theorem compact_localValue_quadratic_bound (hD : OrdinaryH1Density)
    {K : ℝ} (hS : OrdinarySobolev K) {Q : Set EnergyState} (hQ : IsCompact Q)
    {χ : Space → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {η : ℝ} (hη : 0 < η) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ) (y : Space) (h : EnergyState),
      h ∈ Q → ‖compactLocalValue hχ hc (criticalAffineState ρ hρ y h)‖ ^ 2 ≤
        2 * ‖compactLocalValue hχ hc‖ ^ 2 * η ^ 2 + 2 * ρ ^ 2 * L := by
  obtain ⟨L, hL, hb⟩ := compact_localValue_finite_net_bound hD hS hQ hχ hc hη
  refine ⟨L ^ 2, sq_nonneg _, ?_⟩
  intro ρ hρ y h hh
  have hp := pow_le_pow_left₀ (norm_nonneg _) (hb ρ hρ y h hh) 2
  nlinarith [sq_nonneg (‖compactLocalValue hχ hc‖ * η - ρ * L)]

/-- Choose the compact-smooth error before the physical scale.
There is no restriction, regularity condition, or limiting condition on the center. -/
theorem compact_localValue_small (hD : OrdinaryH1Density)
    {K : ℝ} (hS : OrdinarySobolev K) {Q : Set EnergyState} (hQ : IsCompact Q)
    {χ : Space → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ < δ →
      ∀ (y : Space) (h : EnergyState), h ∈ Q →
        ‖compactLocalValue hχ hc (criticalAffineState ρ hρ y h)‖ < ε := by
  let C : ℝ := ‖compactLocalValue hχ hc‖
  have hC : 0 ≤ C := ContinuousLinearMap.opNorm_nonneg (compactLocalValue hχ hc)
  have hCp : 0 < C + 1 := by linarith
  let η : ℝ := ε / (2 * (C + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨L, hL, hb⟩ := compact_localValue_finite_net_bound hD hS hQ hχ hc hη
  have hLp : 0 < L + 1 := by linarith
  let δ : ℝ := ε / (2 * (L + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro ρ hρ hρδ y h hh
  have hfirst : C * η < ε / 2 := by
    have hid : (C + 1) * η = ε / 2 := by
      dsimp [η]
      field_simp [ne_of_gt hCp]
    nlinarith
  have hsecond : ρ * L < ε / 2 := by
    have hid : δ * (L + 1) = ε / 2 := by
      dsimp [δ]
      field_simp [ne_of_gt hLp]
    have hlt := mul_lt_mul_of_pos_right hρδ hLp
    nlinarith
  exact (hb ρ hρ y h hh).trans_lt (by change C * η + ρ * L < ε; linarith)

/-- The actual accepted charge operator, with the same original EnergyState and cutoff. -/
theorem compact_physicalChargeValue_small (hD : OrdinaryH1Density)
    {K : ℝ} (hS : OrdinarySobolev K) {Q : Set EnergyState} (hQ : IsCompact Q)
    {R : ℝ} (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : ℝ) (hρ : 0 < ρ), ρ < δ →
      ∀ (y : Space) (h : EnergyState), h ∈ Q →
        ‖physicalChargeValue hR (criticalAffineState ρ hρ y h)‖ < ε := by
  exact compact_localValue_small hD hS hQ
    (Real.continuous_sqrt.comp (chargeCutoff_smooth R).continuous)
    ((chargeCutoff_compact hR).comp_left Real.sqrt_zero) hε

/-- Exact original spatialCharge is the square of this local L2 norm. -/
theorem spatialCharge_eq_norm_sq {R : ℝ} (hR : 0 < R) (h : EnergyState) :
    spatialCharge R (energyValue h) = ‖physicalChargeValue hR h‖ ^ 2 := by
  rw [(original_spatialCharge_form hR h).2]
  change inner ℝ (physicalChargeValue hR h) (physicalChargeValue hR h) = _
  exact real_inner_self_eq_norm_sq _

/-- Arbitrary varying normalized data and centers; only the physical scale tends to zero. -/
theorem compact_physicalChargeValue_tendsto_zero (hD : OrdinaryH1Density)
    {K : ℝ} (hS : OrdinarySobolev K) {Q : Set EnergyState} (hQ : IsCompact Q)
    {R : ℝ} (hR : 0 < R) {ι : Type*} (l : Filter ι)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (y : ι → Space)
    (v : ι → EnergyState) (hv : ∀ i, v i ∈ Q)
    (hcollapse : Tendsto ρ l (𝓝 0)) :
    Tendsto (fun i => physicalChargeValue hR
      (criticalAffineState (ρ i) (hρ i) (y i) (v i))) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := compact_physicalChargeValue_small hD hS hQ hR hε
  filter_upwards [hcollapse.eventually_lt_const hδ] with i hi
  simpa only [dist_zero_right] using hsmall (ρ i) (hρ i) hi (y i) (v i) (hv i)

/-- The finite-endpoint exit for the literal accepted chi_R scalar spatial integral. -/
theorem compact_spatialCharge_tendsto_zero (hD : OrdinaryH1Density)
    {K : ℝ} (hS : OrdinarySobolev K) {Q : Set EnergyState} (hQ : IsCompact Q)
    {R : ℝ} (hR : 0 < R) {ι : Type*} (l : Filter ι)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (y : ι → Space)
    (v : ι → EnergyState) (hv : ∀ i, v i ∈ Q)
    (hcollapse : Tendsto ρ l (𝓝 0)) :
    Tendsto (fun i => spatialCharge R
      (energyValue (criticalAffineState (ρ i) (hρ i) (y i) (v i)))) l (𝓝 0) := by
  simp_rw [spatialCharge_eq_norm_sq hR]
  simpa only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
    (compact_physicalChargeValue_tendsto_zero hD hS hQ hR l ρ hρ y v hv hcollapse).norm.pow 2

/-- Direct integer-radius output for the subsequent nonnegative-Fatou consumer. -/
theorem compact_integer_spatialCharge_tendsto_zero (hD : OrdinaryH1Density)
    {K : ℝ} (hS : OrdinarySobolev K) {Q : Set EnergyState} (hQ : IsCompact Q)
    (n : ℕ) {ι : Type*} (l : Filter ι)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (y : ι → Space)
    (v : ι → EnergyState) (hv : ∀ i, v i ∈ Q)
    (hcollapse : Tendsto ρ l (𝓝 0)) :
    Tendsto (fun i => spatialCharge ((n : ℝ) + 1)
      (energyValue (criticalAffineState (ρ i) (hρ i) (y i) (v i)))) l (𝓝 0) :=
  compact_spatialCharge_tendsto_zero hD hS hQ (by positivity) l ρ hρ y v hv hcollapse

#print axioms compact_smooth_finite_net
#print axioms criticalSmoothL2_same_value
#print axioms compact_localValue_quadratic_bound
#print axioms compact_physicalChargeValue_small
#print axioms compact_spatialCharge_tendsto_zero
#print axioms compact_integer_spatialCharge_tendsto_zero
end HartreeF.CompactLocalMass
