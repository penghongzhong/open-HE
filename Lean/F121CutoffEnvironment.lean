import F121CutoffMaps
import F121SchwartzConvolutionSmooth

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology ZeroAtInfty
namespace HartreeF.Paper121CutoffEnvironment
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open PhysicalLowpass YoungSource Paper121CutoffCore Paper121CutoffMaps Paper121Annular

/-- A single constant for both low and annular estimates, independent of M and u. -/
def cutoffBoundConstant (q : Cutoff) (K : ℝ) : ℝ :=
  1+|cutoffYoungConstant q*K^((6 : ℝ)⁻¹)|+|10*cutoffL2Constant q|

theorem cutoffBoundConstant_bounds (q : Cutoff) (K : ℝ) :
    0 < cutoffBoundConstant q K ∧
    cutoffYoungConstant q*K^((6 : ℝ)⁻¹) ≤ cutoffBoundConstant q K ∧
    10*cutoffL2Constant q ≤ cutoffBoundConstant q K := by
  unfold cutoffBoundConstant
  constructor
  · linarith [abs_nonneg (cutoffYoungConstant q*K^((6 : ℝ)⁻¹)), abs_nonneg (10*cutoffL2Constant q)]
  constructor
  · linarith [le_abs_self (cutoffYoungConstant q*K^((6 : ℝ)⁻¹)), abs_nonneg (10*cutoffL2Constant q)]
  · linarith [le_abs_self (10*cutoffL2Constant q), abs_nonneg (cutoffYoungConstant q*K^((6 : ℝ)⁻¹))]

/-- Lemma 6.1: the literal representatives and every displayed bound, for the same bounded
linear operators. Ordinary density and Sobolev are the retained standard analysis inputs. -/
theorem lemma61_full_environment (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (hM : 0 < M) (u : EnergyState),
      (∀ x : V, cutoffKernel q hM x =
        M^3 • cutoffKernel q (L := 1) (by norm_num) (M • x)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (convolutionValue (cutoffKernel q hM) (energyValue u)) ∧
      (convolutionValue (cutoffKernel q hM) (energyValue u) =ᵐ[volume]
        energyValue (lowEnergyCLM hDensity hSob q hM u)) ∧
      (Lp.toTemperedDistribution (lowInfinityCLM q hM u) =
        low q M (energyDistribution u)) ∧
      (Lp.toTemperedDistribution (highValueL2CLM hDensity hSob q hM u) =
        high q M (energyDistribution u)) ∧
      (∀ v : L2, Lp.toTemperedDistribution v = high q M (energyDistribution u) →
        v = highValueL2CLM hDensity hSob q hM u) ∧
      ((energyValue (highEnergyCLM hDensity hSob q hM u) : V → ℂ) =ᵐ[volume]
        highValueL2CLM hDensity hSob q hM u) ∧
      pureGradientNorm (lowEnergyCLM hDensity hSob q hM u) ≤ pureGradientNorm u ∧
      pureGradientNorm (highEnergyCLM hDensity hSob q hM u) ≤ pureGradientNorm u ∧
      pureGradientNorm (lowEnergyCLM hDensity hSob q hM u)+
        pureGradientNorm (highEnergyCLM hDensity hSob q hM u) ≤ 2*pureGradientNorm u ∧
      ‖highValueL2CLM hDensity hSob q hM u‖ ≤ M⁻¹*pureGradientNorm u ∧
      ‖lowInfinityCLM q hM u‖ ≤ C*Real.sqrt M*pureGradientNorm u ∧
      (∀ x : V, ‖convolutionValue (cutoffKernel q hM) (energyValue u) x‖ ≤
        C*Real.sqrt M*pureGradientNorm u) ∧
      (Lp.toTemperedDistribution (annularValueL2CLM hDensity hSob q hM u) =
        low q M (energyDistribution u)-low q (M/2) (energyDistribution u)) ∧
      ‖annularValueL2CLM hDensity hSob q hM u‖ ≤ (2*M⁻¹)*pureGradientNorm u ∧
      ‖annularInfinityCLM hDensity hSob q hM u‖ ≤ C*Real.sqrt M*pureGradientNorm u ∧
      ((annularC0CLM hDensity hSob q hM u : V → ℂ) =ᵐ[volume]
        annularValueL2CLM hDensity hSob q hM u) ∧
      Continuous (annularC0CLM hDensity hSob q hM u : V → ℂ) ∧
      Tendsto (annularC0CLM hDensity hSob q hM u : V → ℂ) (cocompact V) (𝓝 0) ∧
      (∀ x : V, ‖annularC0CLM hDensity hSob q hM u x‖ ≤ C*Real.sqrt M*pureGradientNorm u) ∧
      (∀ ξ : V, (lowSymbol q M ξ-lowSymbol q (M/2) ξ)*
        (lowSymbol q (2*M) ξ-lowSymbol q (M/4) ξ) = lowSymbol q M ξ-lowSymbol q (M/2) ξ) := by
  obtain ⟨hC, hLow, hAnn⟩ := cutoffBoundConstant_bounds q K
  refine ⟨cutoffBoundConstant q K, hC, ?_⟩
  intro M hM u
  have low_le : (cutoffYoungConstant q*K^((6 : ℝ)⁻¹))*Real.sqrt M*pureGradientNorm u ≤
      cutoffBoundConstant q K*Real.sqrt M*pureGradientNorm u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLow (Real.sqrt_nonneg M))
      (pureGradientNorm_nonneg u)
  have ann_le : (10*cutoffL2Constant q)*Real.sqrt M*pureGradientNorm u ≤
      cutoffBoundConstant q K*Real.sqrt M*pureGradientNorm u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAnn (Real.sqrt_nonneg M))
      (pureGradientNorm_nonneg u)
  refine ⟨cutoffKernel_scale q hM, Paper121SmoothConvolution.low_convolution_smooth q hM u,
    low_convolution_same_value hDensity hSob q hM u, ?_,
    highValueL2_distribution hDensity hSob q hM u,
    highValueL2_unique hDensity hSob q hM u,
    highEnergyState_value_ae hDensity hSob q hM u,
    low_gradient_contraction hDensity hSob q hM u,
    highEnergyState_pureGradient_bound hDensity hSob q hM u,
    gradient_pair_bound hDensity hSob q hM u,
    highValueL2_bound hDensity hSob q hM u,
    (lowInfinity_gradient_bound hSob q hM u).trans low_le,
    (fun x => (low_convolution_gradient_bound hSob q hM u x).trans low_le),
    annular_l2_distribution hDensity hSob q hM u,
    annular_l2_bound hDensity hSob q hM u,
    (annularInfinity_gradient_bound hDensity hSob q hM u).trans ann_le,
    annular_C0_same_L2 hDensity hSob q hM u, map_continuous _, zero_at_infty _,
    (fun x => (annular_C0_gradient_bound hDensity hSob q hM u x).trans ann_le),
    annular_symbol_reproduction q hM⟩
  exact (low_convolution_same_distribution hDensity hSob q hM u).trans
    (lowEnergyState_distribution hDensity hSob q hM u)

end HartreeF.Paper121CutoffEnvironment
