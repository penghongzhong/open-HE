import FExactLocalFluxBound
import CutoffNorm
import FEnergyGradientNorm

/-!
Pre-L2 uniform local-charge flux bound for the literal spatial charge cutoffs.
Only positive integer radii R = n + 1 are asserted. They suffice for the cutoff
exhaustion/Fatou argument. No L2 representative of the original value is used.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal Topology
namespace HartreeF.LocalDualSource
open EnergySpace LocalChargeBridge LocalChargeRigidity CutoffApproximation SobolevStretch

/-- The exact same fixed bump, at the integer radii used in exhaustion. -/
theorem chargeCutoff_nat_succ_eq_cutoff (n : ℕ) :
    chargeCutoff ((n : ℝ) + 1) = cutoff n := rfl

/-- Finite critical norm of the actual fixed cutoff gradient. -/
def baseGradientL3Norm : ℝ :=
  (eLpNorm (gradient (baseBump : V → ℝ)) 3 volume).toReal

theorem baseGradientL3Norm_nonneg : 0 ≤ baseGradientL3Norm :=
  ENNReal.toReal_nonneg

/-- The actual coordinate coefficient has a radius-independent L3 norm.
Only almost-everywhere equality of the Lp representative is used. -/
theorem chargeCutoff_coefficientLp_norm (n : ℕ) (j : Fin 3) :
    ‖coefficientLp
      (coefficientDerivative_continuous (chargeCutoff_smooth ((n : ℝ) + 1)) j)
      (coefficientDerivative_compact (chargeCutoff_compact (by positivity :
        0 < (n : ℝ) + 1)) j) 3‖ ≤ baseGradientL3Norm := by
  let hχ := chargeCutoff_smooth ((n : ℝ) + 1)
  let hc := chargeCutoff_compact (by positivity : 0 < (n : ℝ) + 1)
  let a := coefficientLp (coefficientDerivative_continuous hχ j)
    (coefficientDerivative_compact hc j) 3
  change ‖a‖ ≤ baseGradientL3Norm
  rw [Lp.norm_def]
  apply ENNReal.toReal_mono cutoff_gradient_eLpNorm_lt_top.ne
  calc
    eLpNorm (a : V → ℂ) 3 volume ≤
        eLpNorm (gradient (chargeCutoff ((n : ℝ) + 1))) 3 volume := by
      apply eLpNorm_mono_ae (Lp.aestronglyMeasurable a)
      filter_upwards [coefficientLp_ae (coefficientDerivative_continuous hχ j)
        (coefficientDerivative_compact hc j) 3] with x hx
      change a x = _ at hx
      rw [hx, Complex.norm_real, coefficientDerivative_eq_gradient_coordinate]
      exact PiLp.norm_apply_le _ _
    _ = eLpNorm (gradient (baseBump : V → ℝ)) 3 volume := by
      rw [chargeCutoff_nat_succ_eq_cutoff, cutoff_gradient_eLpNorm]

/-- The coordinate flux pairs an original L2 weak gradient with cutoff times
an original L6 value. There is no global L2 hypothesis on that value. -/
theorem originalFlux_coordinate_le_coefficient {χ : V → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (u : EnergyState) (j : Fin 3) :
    |(∫ x : V, fluxIntegrand (χ := χ) u j x).im| ≤
      ‖coefficientLp (coefficientDerivative_continuous hχ j)
        (coefficientDerivative_compact hc j) 3‖ * ‖energyValue u‖ *
        ‖energyGradient j u‖ := by
  let D := cutoffL6L2 (coefficientDerivative_continuous hχ j)
    (coefficientDerivative_compact hc j) (energyValue u)
  have he : (∫ x : V, fluxIntegrand (χ := χ) u j x) =
      inner ℂ D (energyGradient j u) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [cutoffL6L2_ae (coefficientDerivative_continuous hχ j)
      (coefficientDerivative_compact hc j) (energyValue u)] with x hx
    change D x = _ at hx
    change fluxIntegrand (χ := χ) u j x = energyGradient j u x * star (D x)
    rw [hx]
    apply Complex.ext <;>
      simp [fluxIntegrand, Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring
  rw [he]
  calc
    |(inner ℂ D (energyGradient j u)).im| ≤ ‖inner ℂ D (energyGradient j u)‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ‖D‖ * ‖energyGradient j u‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (cutoffL6L2_norm (coefficientDerivative_continuous hχ j)
        (coefficientDerivative_compact hc j) (energyValue u)) (norm_nonneg _)

/-- Explicit constant, independent of radius and state. The harmless factor
six is two from the charge derivative and three from the coordinate sum. -/
def uniformChargeFluxConstant (K : ℝ) : ℝ :=
  6 * baseGradientL3Norm * K ^ ((6 : ℝ)⁻¹)

theorem uniformChargeFluxConstant_nonneg {K : ℝ} (hSob : OrdinarySobolev K) :
    0 ≤ uniformChargeFluxConstant K := by
  unfold uniformChargeFluxConstant
  exact mul_nonneg (mul_nonneg (by norm_num) baseGradientL3Norm_nonneg)
    (Real.rpow_nonneg hSob.nonneg _)

/-- Genuine pre-L2 local flux estimate at every exhausting radius. It consumes
only ordinary Sobolev and the original EnergyState weak-gradient structure. -/
theorem originalFlux_uniform_nat_bound {K : ℝ} (hSob : OrdinarySobolev K)
    (n : ℕ) (u : EnergyState) :
    |2 * ∑ j : Fin 3, (∫ x : V,
      fluxIntegrand (χ := chargeCutoff ((n : ℝ) + 1)) u j x).im| ≤
      uniformChargeFluxConstant K * pureGradientNorm u ^ 2 := by
  have hc (j : Fin 3) :
      |(∫ x : V, fluxIntegrand (χ := chargeCutoff ((n : ℝ) + 1)) u j x).im| ≤
        baseGradientL3Norm * K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u ^ 2 := by
    calc
      _ ≤ ‖coefficientLp
          (coefficientDerivative_continuous (chargeCutoff_smooth ((n : ℝ) + 1)) j)
          (coefficientDerivative_compact (chargeCutoff_compact (by positivity :
            0 < (n : ℝ) + 1)) j) 3‖ * ‖energyValue u‖ * ‖energyGradient j u‖ :=
        originalFlux_coordinate_le_coefficient (chargeCutoff_smooth ((n : ℝ) + 1))
          (chargeCutoff_compact (by positivity)) u j
      _ ≤ (baseGradientL3Norm * (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u)) *
          pureGradientNorm u := by
        apply mul_le_mul
        · exact mul_le_mul (chargeCutoff_coefficientLp_norm n j)
            (energyValue_le_pureGradient hSob u) (norm_nonneg _) baseGradientL3Norm_nonneg
        · exact energyGradient_le_pureGradient u j
        · exact norm_nonneg _
        · exact mul_nonneg baseGradientL3Norm_nonneg
            (mul_nonneg (Real.rpow_nonneg hSob.nonneg _) (pureGradientNorm_nonneg u))
      _ = _ := by ring
  calc
    _ = 2 * |∑ j : Fin 3, (∫ x : V,
        fluxIntegrand (χ := chargeCutoff ((n : ℝ) + 1)) u j x).im| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ∑ j : Fin 3, |(∫ x : V,
        fluxIntegrand (χ := chargeCutoff ((n : ℝ) + 1)) u j x).im| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2 * ∑ _j : Fin 3,
        (baseGradientL3Norm * K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hc j)) (by norm_num)
    _ = uniformChargeFluxConstant K * pureGradientNorm u ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        uniformChargeFluxConstant]
      ring

/-- Ready for the original local-charge exhaustion, before proving any L2 mass. -/
theorem exists_originalFlux_uniform_nat_bound {K : ℝ} (hSob : OrdinarySobolev K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (u : EnergyState),
      |2 * ∑ j : Fin 3, (∫ x : V,
        fluxIntegrand (χ := chargeCutoff ((n : ℝ) + 1)) u j x).im| ≤
          C * pureGradientNorm u ^ 2 :=
  ⟨uniformChargeFluxConstant K, uniformChargeFluxConstant_nonneg hSob,
    originalFlux_uniform_nat_bound hSob⟩

#print axioms originalFlux_uniform_nat_bound
#print axioms exists_originalFlux_uniform_nat_bound
end HartreeF.LocalDualSource
