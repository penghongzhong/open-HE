import FActualCompactConjugateTest
import FPhysicalChargeDualIdentification

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
open MeasureTheory Filter Set LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.LocalDualSource
open EnergySpace LocalChargeBridge LocalChargeRigidity ForcingDomain ForcingContinuity

local instance green_source_ge_one : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩

/-- First integration by parts is inherited from the actual EnergyState graph. -/
theorem energyDistribution_lineDeriv_test (u : EnergyState) (j : Fin 3) (ψ : Test) :
    energyDistribution u (∂_{coordinate j} ψ) =
      -(∫ x : V, ψ x * energyGradient j u x) := by
  have h := congrArg (fun T : TD => T ψ) (energyDistribution_derivative u j)
  change (∂_{coordinate j} (Lp.toTemperedDistribution (energyValue u))) ψ =
    Lp.toTemperedDistribution (energyGradient j u) ψ at h
  simp only [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    neg_apply, smul_eq_mul, neg_mul, integral_neg] at h
  change Lp.toTemperedDistribution (energyValue u) (∂_{coordinate j} ψ) = _
  rw [Lp.toTemperedDistribution_apply]
  simpa only [smul_eq_mul] using neg_eq_iff_eq_neg.mp h

/-- Actual Euclidean three-coordinate Green identity, obtained from distributional derivatives. -/
theorem energyDistribution_laplacian_test (u : EnergyState) (ψ : Test) :
    energyDistribution u (Δ ψ) =
      -(∑ j : Fin 3, ∫ x : V, (∂_{coordinate j} ψ) x * energyGradient j u x) := by
  rw [SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ), map_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [EuclideanSpace.basisFun_apply, coordinate] using
    energyDistribution_lineDeriv_test u j (∂_{coordinate j} ψ)

variable {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)

/-- The value test is the actual complex localized pairing, with original representatives. -/
theorem energyDistribution_compactConjugateTest (u : EnergyState) (φ : Test) :
    energyDistribution u (compactConjugateTest hχ hc φ) =
      ∫ x : V, (χ x : ℂ) * energyValue u x * star (energyValue (schwartzEnergyState φ) x) := by
  change Lp.toTemperedDistribution (energyValue u) _ = _
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [schwartzEnergyState_value_ae φ] with x hx
  rw [compactConjugateTest_apply, hx]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

/-- The actual compact conjugate test realizes the kinetic term without any Green premise. -/
theorem energyDistribution_compactConjugateTest_laplacian (u : EnergyState) (φ : Test) :
    energyDistribution u (Δ (compactConjugateTest hχ hc φ)) =
      -(∑ j : Fin 3, ∫ x : V, kineticIntegrand (χ := χ) u (schwartzEnergyState φ) j x) := by
  rw [energyDistribution_laplacian_test]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [compactConjugateTest_derivative_ae hχ hc φ j] with x hx
  rw [hx]
  exact mul_comm _ _

/-- The literal Hartree forcing distribution is the already constructed actual source dual. -/
theorem forcingDistribution_compactConjugateTest {α c : ℝ} (hH : OrdinaryHLS α c)
    (u : EnergyState) (φ : Test) :
    Lp.toTemperedDistribution (forcingLp hH (energyValue u)) (compactConjugateTest hχ hc φ) =
      sourceToDualCLM hχ hc (forcingLp hH (energyValue u)) (schwartzEnergyState φ) := by
  rw [Lp.toTemperedDistribution_apply, sourceToDualCLM_eq_integral hχ hc hH]
  apply integral_congr_ae
  filter_upwards [(forcing_memLp hH (Lp.memLp (energyValue u))).coeFn_toLp,
    schwartzEnergyState_value_ae φ] with x hf hv
  change (compactConjugateTest hχ hc φ x) * forcingLp hH (energyValue u) x = _
  rw [compactConjugateTest_apply, show forcingLp hH (energyValue u) x = _ from hf]
  simp only [sourceIntegrand, hv, star_smul, star_trivial]
  exact mul_comm _ _

/-- Exact compact weak spatial PDE right-hand side, with both genuine differential operators. -/
theorem spatialWeakForm_eq_distribution {α c : ℝ} (hH : OrdinaryHLS α c)
    (u : EnergyState) (φ : Test) :
    spatialWeakForm (χ := χ) α c u (schwartzEnergyState φ) =
      energyDistribution u (Δ (compactConjugateTest hχ hc φ)) +
        Lp.toTemperedDistribution (forcingLp hH (energyValue u)) (compactConjugateTest hχ hc φ) := by
  rw [energyDistribution_compactConjugateTest_laplacian hχ hc,
    forcingDistribution_compactConjugateTest hχ hc hH, sourceToDualCLM_eq_integral hχ hc hH]
  rfl

/-- The constructed real dual agrees with the literal compact spatial PDE evaluation. -/
theorem actualPDEDual_eq_distribution {α c : ℝ} (hH : OrdinaryHLS α c)
    (u : EnergyState) (φ : Test) :
    actualPDEDual hχ hc hH u (schwartzEnergyState φ) =
      (Complex.I * (energyDistribution u (Δ (compactConjugateTest hχ hc φ)) +
        Lp.toTemperedDistribution (forcingLp hH (energyValue u)) (compactConjugateTest hχ hc φ))).re := by
  rw [actualPDEDual_apply, spatialWeakForm_eq_distribution hχ hc hH]

/-- Exact original physical cutoff pairing, on every original EnergyState and Schwartz test. -/
theorem physicalChargeForm_eq_compactConjugateTest {R : ℝ} (hR : 0 < R)
    (u : EnergyState) (φ : Test) :
    physicalChargeForm hR u (schwartzEnergyState φ) =
      (energyDistribution u
        (compactConjugateTest (chargeCutoff_smooth R) (chargeCutoff_compact hR) φ)).re := by
  rw [physicalChargeForm_eq_integral, energyDistribution_compactConjugateTest]
  rfl

end HartreeF.LocalDualSource
