import FCriticalAffineWeakGradient
import FEnergyGradientNorm
import FEnergySchwartzDensity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.CriticalAffine
open SobolevStretch EnergySpace WeakHartreeProduct
attribute [local irreducible] energySubmodule

/-- A genuine canonical homogeneous state, produced by the proved weak chain rule. -/
def affineState {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) : EnergyState :=
  inDotEnergyState (inDotH1_affine_pullback (energyState_inDotH1 u) ha b)

theorem affineState_value_ae {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    (energyValue (affineState ha b u) : Space → ℂ) =ᵐ[volume]
      valuePullback a b (energyValue u) :=
  inDotEnergyState_value_ae (inDotH1_affine_pullback (energyState_inDotH1 u) ha b)

theorem directionalField_gradientPullback (a : ℝ) (b : Space) (U V : Space → Space) (v : Space) :
    directionalField (gradientPullback a b U) (gradientPullback a b V) v =
      gradientPullback a b (directionalField U V v) := by
  funext x
  apply Complex.ext <;>
    simp [directionalField, gradientPullback, real_inner_smul_left, Complex.real_smul]

theorem affineState_gradient_ae {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) (j : Fin 3) :
    (energyGradient j (affineState ha b u) : Space → ℂ) =ᵐ[volume]
      gradientPullback a b (energyGradient j u) := by
  have h := inDotEnergyState_gradient_ae (inDotH1_affine_pullback (energyState_inDotH1 u) ha b) j
  simpa only [affineState, directionalField_gradientPullback,
    state_directionalField_coordinate] using h

theorem affineState_value_norm {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    ‖energyValue (affineState ha b u)‖ = ‖energyValue u‖ := by
  let : Fact ((1 : ℝ≥0∞) ≤ (6 : ℕ)) := ⟨by norm_num⟩
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : (6:ℕ) ≠ 0)).mp
  rw [energyLp_norm_pow (by decide : (6:ℕ) ≠ 0), energyLp_norm_pow (by decide : (6:ℕ) ≠ 0)]
  calc
    _ = ∫ x, ‖valuePullback a b (energyValue u) x‖^6 := by
      apply integral_congr_ae
      exact (affineState_value_ae ha b u).mono (fun _ h => congrArg (fun z : ℂ => ‖z‖^6) h)
    _ = _ := valuePullback_sixth_integral ha b _

theorem affineState_gradient_norm {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) (j : Fin 3) :
    ‖energyGradient j (affineState ha b u)‖ = ‖energyGradient j u‖ := by
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : (2:ℕ) ≠ 0)).mp
  rw [energyLp_norm_pow (by decide : (2:ℕ) ≠ 0), energyLp_norm_pow (by decide : (2:ℕ) ≠ 0)]
  calc
    _ = ∫ x, ‖gradientPullback a b (energyGradient j u) x‖^2 := by
      apply integral_congr_ae
      exact (affineState_gradient_ae ha b u j).mono (fun _ h => congrArg (fun z : ℂ => ‖z‖^2) h)
    _ = _ := gradientPullback_square_integral ha b _

theorem affineState_gradientSquared {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    gradientSquared (affineState ha b u) = gradientSquared u := by
  simp only [gradientSquared, affineState_gradient_norm]

theorem affineState_pureGradientNorm {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    pureGradientNorm (affineState ha b u) = pureGradientNorm u := by
  simp only [pureGradientNorm, affineState_gradientSquared]

theorem affineState_norm {a : ℝ} (ha : 0 < a) (b : Space) (u : EnergyState) :
    ‖affineState ha b u‖ = ‖u‖ := by
  rw [energyState_norm_eq_max, energyState_norm_eq_max, affineState_value_norm]
  congr 1
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    change ‖energyGradient j (affineState ha b u)‖ ≤ ‖u.val.2‖
    rw [affineState_gradient_norm]
    exact norm_le_pi_norm u.val.2 j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    change ‖energyGradient j u‖ ≤ ‖(affineState ha b u).val.2‖
    rw [← affineState_gradient_norm ha b u j]
    exact norm_le_pi_norm (affineState ha b u).val.2 j

#print axioms affineState
#print axioms affineState_value_ae
#print axioms affineState_gradient_ae
#print axioms affineState_value_norm
#print axioms affineState_gradient_norm
#print axioms affineState_gradientSquared
#print axioms affineState_pureGradientNorm
#print axioms affineState_norm
end HartreeF.CriticalAffine
