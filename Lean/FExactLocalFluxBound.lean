import FActualDualDiagonalFlux
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal Topology
namespace HartreeF.LocalDualSource
open EnergySpace LocalChargeBridge LocalChargeRigidity

/-- The genuine contraction of all three original coordinate gradients. -/
def contractedGradient (χ : V → ℝ) (u : EnergyState) (x : V) : ℂ :=
  ∑ j : Fin 3, coefficientDerivative χ j x • energyGradient j u x

theorem coefficientDerivative_eq_gradient_coordinate (χ : V → ℝ)
    (j : Fin 3) (x : V) :
    coefficientDerivative χ j x = gradient χ x j := by
  rw [coefficientDerivative, ← inner_gradient_left]
  simp only [coordinate, EuclideanSpace.inner_single_right, conj_trivial, one_mul]

theorem coefficientDerivative_sum_sq (χ : V → ℝ) (x : V) :
    (∑ j : Fin 3, |coefficientDerivative χ j x| ^ 2) = ‖gradient χ x‖ ^ 2 := by
  simp only [coefficientDerivative_eq_gradient_coordinate, sq_abs,
    EuclideanSpace.real_norm_sq_eq]

/-- Squared, full Euclidean Cauchy-Schwarz. No coordinate-max comparison. -/
theorem contractedGradient_pointwise_sq (χ : V → ℝ) (u : EnergyState) (x : V) :
    ‖contractedGradient χ u x‖ ^ 2 ≤
      ‖gradient χ x‖ ^ 2 * ∑ j : Fin 3, ‖energyGradient j u x‖ ^ 2 := by
  have ht : ‖contractedGradient χ u x‖ ≤
      ∑ j : Fin 3, |coefficientDerivative χ j x| * ‖energyGradient j u x‖ := by
    simpa only [contractedGradient, norm_smul, Real.norm_eq_abs] using
      norm_sum_le Finset.univ
        (fun j : Fin 3 => coefficientDerivative χ j x • energyGradient j u x)
  calc
    ‖contractedGradient χ u x‖ ^ 2 ≤
        (∑ j : Fin 3, |coefficientDerivative χ j x| * ‖energyGradient j u x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ht 2
    _ ≤ (∑ j : Fin 3, |coefficientDerivative χ j x| ^ 2) *
        ∑ j : Fin 3, ‖energyGradient j u x‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by rw [coefficientDerivative_sum_sq]

theorem contractedGradient_memLp {χ : V → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (u : EnergyState) :
    MemLp (contractedGradient χ u) 2 volume := by
  unfold contractedGradient
  exact memLp_finsetSum Finset.univ (fun j _ =>
    WeakCutoffLp.cutoff_smul_memLp (coefficientDerivative_continuous hχ j)
      (coefficientDerivative_compact hc j) (Lp.memLp (energyGradient j u)))

/-- An actual L2 class, with the precise raw contraction as representative. -/
def contractedGradientL2 {χ : V → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (u : EnergyState) : L2 :=
  (contractedGradient_memLp hχ hc u).toLp (contractedGradient χ u)

theorem contractedGradientL2_ae {χ : V → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (u : EnergyState) :
    (contractedGradientL2 hχ hc u : V → ℂ) =ᵐ[volume] contractedGradient χ u :=
  MemLp.coeFn_toLp _

/-- Integrate the squared Euclidean estimate with its exact cutoff bound. -/
theorem contractedGradientL2_norm {χ : V → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x : V, ‖gradient χ x‖ ≤ C)
    (u : EnergyState) :
    ‖contractedGradientL2 hχ hc u‖ ≤ C * pureGradientNorm u := by
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  let G := contractedGradientL2 hχ hc u
  have hi (j : Fin 3) : Integrable (fun x : V => ‖energyGradient j u x‖ ^ 2) volume :=
    (Lp.memLp (energyGradient j u)).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hiSum := integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hsq : ‖G‖ ^ 2 ≤ C ^ 2 * gradientSquared u := by
    calc
      ‖G‖ ^ 2 = ∫ x : V, ‖G x‖ ^ 2 := energyLp_norm_pow (n := 2) (by decide) G
      _ ≤ ∫ x : V, C ^ 2 * ∑ j : Fin 3, ‖energyGradient j u x‖ ^ 2 := by
        apply integral_mono_ae
          ((Lp.memLp G).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
          (hiSum.const_mul (C ^ 2))
        filter_upwards [contractedGradientL2_ae hχ hc u] with x hx
        change G x = contractedGradient χ u x at hx
        rw [hx]
        exact (contractedGradient_pointwise_sq χ u x).trans
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2)
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      _ = C ^ 2 * gradientSquared u := by
        rw [integral_const_mul, integral_finsetSum _ (fun j _ => hi j)]
        unfold gradientSquared
        congr 1
        exact Finset.sum_congr rfl (fun j _ =>
          (energyLp_norm_pow (n := 2) (by decide) (energyGradient j u)).symm)
  apply (sq_le_sq₀ (norm_nonneg G)
    (mul_nonneg hC (pureGradientNorm_nonneg u))).mp
  simpa only [mul_pow, pureGradientNorm_sq] using hsq

/-- The actual complex integral is the ordinary complex L2 inner product. -/
theorem originalFlux_sum_eq_inner {χ : V → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (u : EnergyState) (v : L2) (hSame : (v : V → ℂ) =ᵐ[volume] energyValue u) :
    (∑ j : Fin 3, ∫ x : V, fluxIntegrand (χ := χ) u j x) =
      inner ℂ v (contractedGradientL2 hχ hc u) := by
  rw [MeasureTheory.L2.inner_def,
    ← integral_finsetSum _ (fun j _ => fluxIntegrand_integrable hχ hc u j)]
  apply integral_congr_ae
  filter_upwards [contractedGradientL2_ae hχ hc u, hSame] with x hx hv
  change (∑ j : Fin 3, fluxIntegrand (χ := χ) u j x) =
    contractedGradientL2 hχ hc u x * star (v x)
  rw [hx, hv]
  simp only [contractedGradient, Finset.sum_mul, Complex.real_smul, fluxIntegrand]

/-- Exact physical-space estimate. No source flux inequality is assumed. -/
theorem originalFlux_exact_bound {R : ℝ} (hR : 0 < R)
    (u : EnergyState) (v : L2) (hSame : (v : V → ℂ) =ᵐ[volume] energyValue u) :
    |∑ j : Fin 3, (∫ x : V, fluxIntegrand (χ := chargeCutoff R) u j x).im| ≤
      (baseGradientBound / R) * ‖v‖ * pureGradientNorm u := by
  let hχ := chargeCutoff_smooth R
  let hc := chargeCutoff_compact hR
  let G := contractedGradientL2 hχ hc u
  have hG : ‖G‖ ≤ (baseGradientBound / R) * pureGradientNorm u :=
    contractedGradientL2_norm hχ hc
      (div_nonneg baseGradientBound_nonneg hR.le) (chargeCutoff_gradient_bound hR) u
  have he : (∑ j : Fin 3, (∫ x : V,
      fluxIntegrand (χ := chargeCutoff R) u j x).im) = (inner ℂ v G).im := by
    change (∑ j : Fin 3, Complex.imCLM (∫ x : V,
      fluxIntegrand (χ := chargeCutoff R) u j x)) = Complex.imCLM (inner ℂ v G)
    rw [← map_sum, originalFlux_sum_eq_inner hχ hc u v hSame]
  rw [he]
  calc
    |(inner ℂ v G).im| ≤ ‖inner ℂ v G‖ := Complex.abs_im_le_norm _
    _ ≤ ‖v‖ * ‖G‖ := norm_inner_le_norm (𝕜 := ℂ) v G
    _ ≤ ‖v‖ * ((baseGradientBound / R) * pureGradientNorm u) :=
      mul_le_mul_of_nonneg_left hG (norm_nonneg v)
    _ = _ := by ring

end HartreeF.LocalDualSource
