import FCriticalAffineState
import FStateEnergyCalculus
import RieszPairIntegrability

/-! Exact invariance of the actual Hartree pair interaction and canonical total energy.
Only the already retained ordinary HLS is used for genuine integration domains. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.CriticalAffine
open EnergySpace StateEnergy EnergyVariation ForcingDomain PressureDomain

theorem valuePullback_powerDensity (α : ℝ) {a : ℝ} (ha : 0 < a) (b : Space)
    (u : Space → ℂ) (x : Space) :
    powerDensity α (valuePullback a b u) x =
      a^((3+α)/2) * powerDensity α u (affine a b x) := by
  simp only [powerDensity, valuePullback, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg a)]
  rw [Real.mul_rpow (Real.sqrt_nonneg a) (norm_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul ha.le]
  congr 2
  ring

theorem rieszKernel_affine_sub (α c : ℝ) {a : ℝ} (ha : 0 < a) (b x y : Space) :
    rieszKernel α c (affine a b x-affine a b y) = a^(α-3) * rieszKernel α c (x-y) := by
  have he : affine a b x-affine a b y = a • (x-y) := by simp [affine, smul_sub]
  rw [he]
  simp only [rieszKernel, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    Real.mul_rpow ha.le (norm_nonneg _)]
  ring

theorem pairDensity_affine_pullback (α c : ℝ) {a : ℝ} (ha : 0 < a) (b : Space)
    (u : Space → ℂ) (q : Space × Space) :
    rieszPairDensity α c (valuePullback a b u) q =
      a^6 * rieszPairDensity α c u (affine a b q.1, affine a b q.2) := by
  have hp : a^((3+α)/2) * a^((3+α)/2) = a^(3+α) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have hk : a^6 * a^(α-3) = a^(3+α) := by
    rw [show a^6 = a^(6:ℝ) by simp, ← Real.rpow_add ha]
    congr 1
    ring
  simp only [rieszPairDensity, valuePullback_powerDensity α ha b,
    rieszKernel_affine_sub α c ha b]
  calc
    _ = (a^((3+α)/2) * a^((3+α)/2)) * rieszKernel α c (q.1-q.2) *
      powerDensity α u (affine a b q.2) * powerDensity α u (affine a b q.1) := by ring
    _ = _ := by rw [hp, ← hk]; ring

theorem pair_affine_integral {a : ℝ} (ha : 0 < a) (b : Space) (f : Space × Space → ℝ) :
    (∫ q, f (affine a b q.1, affine a b q.2) ∂volume.prod volume) =
      (a^6)⁻¹ * ∫ q, f q ∂volume.prod volume := by
  change (∫ q : Space × Space, f (a • q+(b,b)) ∂volume.prod volume) = _
  rw [Measure.integral_comp_smul_of_nonneg (volume.prod volume)
    (fun q => f (q+(b,b))) a (hR := ha.le)]
  rw [integral_add_right_eq_self]
  simp [Module.finrank_prod]

/-- HLS produces both pair domains before the exact change of variables. -/
theorem hartree_pair_domain_and_invariance {α c : ℝ} (hH : OrdinaryHLS α c)
    {a : ℝ} (ha : 0 < a) (b : Space) {u : Space → ℂ} (hu : MemLp u 6 volume) :
    Integrable (rieszPairDensity α c u) (volume.prod volume) ∧
    Integrable (rieszPairDensity α c (valuePullback a b u)) (volume.prod volume) ∧
    (∫ q, rieszPairDensity α c (valuePullback a b u) q ∂volume.prod volume) =
      ∫ q, rieszPairDensity α c u q ∂volume.prod volume := by
  refine ⟨rieszPairDensity_integrable hH hu,
    rieszPairDensity_integrable hH (valuePullback_memLp ha b (by norm_num) (by norm_num) hu), ?_⟩
  simp only [pairDensity_affine_pullback α c ha b u, integral_const_mul]
  rw [pair_affine_integral ha b, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]

theorem interaction_valuePullback {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {a : ℝ} (ha : 0 < a) (b : Space) {u : Space → ℂ} (hu : MemLp u 6 volume) :
    DirectionalCoercivity.interaction α (valuePullback a b u) =
      DirectionalCoercivity.interaction α u := by
  unfold DirectionalCoercivity.interaction
  rw [← hartree_energy_pair_identity hH
    (valuePullback_memLp ha b (by norm_num) (by norm_num) hu),
    ← hartree_energy_pair_identity hH hu]
  exact (hartree_pair_domain_and_invariance hH ha b hu).2.2

theorem affineState_interaction {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    interactionLp α (energyValue (affineState ha b u)) = interactionLp α (energyValue u) := by
  unfold interactionLp
  rw [interaction_congr_ae α (affineState_value_ae ha b u)]
  exact interaction_valuePullback hH ha b (Lp.memLp _)

theorem affineState_totalEnergy {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    totalEnergy α (affineState ha b u) = totalEnergy α u := by
  simp only [totalEnergy, affineState_gradientSquared, affineState_interaction hH]

#print axioms valuePullback_powerDensity
#print axioms rieszKernel_affine_sub
#print axioms pairDensity_affine_pullback
#print axioms pair_affine_integral
#print axioms hartree_pair_domain_and_invariance
#print axioms interaction_valuePullback
#print axioms affineState_interaction
#print axioms affineState_totalEnergy
end HartreeF.CriticalAffine
