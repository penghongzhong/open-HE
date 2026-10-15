import F121SchwartzConvolutionSmooth
import F121AnnularRepresentative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal Topology ZeroAtInfty
namespace HartreeF.Paper121CutoffMaps
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open PhysicalLowpass YoungSource Paper121ConvolutionC0 Paper121CutoffCore

local instance : (6 : ℝ≥0∞).HolderConjugate sourceExponent := by
  have h : Real.HolderConjugate 6 (6/5) := by norm_num [Real.holderConjugate_iff]
  simpa [sourceExponent] using h.ennrealOfReal

/-- The homogeneous highpass is a bounded linear map, with its previously constructed value. -/
def highEnergyCLM (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) : EnergyState →L[ℂ] EnergyState where
  toFun := highEnergyState hDensity hSob q hM
  map_add' := by
    intro u v
    apply energyDistribution_injective
    simp only [highEnergyState_distribution, map_add]
  map_smul' := by
    intro c u
    apply energyDistribution_injective
    simp only [highEnergyState_distribution, map_smul, RingHom.id_apply]
  cont := highEnergyState_continuous hDensity hSob q hM

def lowEnergyCLM (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) : EnergyState →L[ℂ] EnergyState :=
  ContinuousLinearMap.id ℂ EnergyState-highEnergyCLM hDensity hSob q hM

theorem lowEnergyCLM_apply (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    lowEnergyCLM hDensity hSob q hM u = lowEnergyState hDensity hSob q hM u := rfl

def lowInfinityCLM (q : Cutoff) {M : ℝ} (hM : 0 < M) :
    EnergyState →L[ℂ] Lp ℂ ∞ (volume : Measure V) :=
  (convolutionInfinityCLM (p := 6) (r := sourceExponent) (cutoffKernel q hM)).comp energyValue

def lowC0CLM (q : Cutoff) {M : ℝ} (hM : 0 < M) : EnergyState →L[ℂ] C₀(V, ℂ) :=
  (convolutionC0 (p := 6) (cutoffKernel q hM)).comp energyValue

theorem lowC0CLM_apply (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) (x : V) :
    lowC0CLM q hM u x = convolutionValue (cutoffKernel q hM) (energyValue u) x :=
  convolutionC0_apply (r := sourceExponent) (by norm_num : (6 : ℝ≥0∞) ≠ ∞) _ _ _

/-- The actual smooth convolution is the low-frequency homogeneous-energy representative. -/
theorem low_convolution_same_value (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    convolutionValue (cutoffKernel q hM) (energyValue u) =ᵐ[volume]
      energyValue (lowEnergyCLM hDensity hSob q hM u) := by
  have ha := CriticalPathSpace.spatial_ae_eq_of_distribution_eq
    (convolutionInfinity (r := sourceExponent) (cutoffKernel q hM) (energyValue u))
    (energyValue (lowEnergyState hDensity hSob q hM u))
    (low_convolution_same_distribution hDensity hSob q hM u)
  exact (convolutionInfinity_coe (r := sourceExponent) (cutoffKernel q hM)
    (energyValue u)).symm.trans ha

theorem lowInfinity_gradient_bound {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    ‖lowInfinityCLM q hM u‖ ≤
      (cutoffYoungConstant q*K^((6 : ℝ)⁻¹))*Real.sqrt M*pureGradientNorm u := by
  change ‖convolutionInfinity (r := sourceExponent) (cutoffKernel q hM) (energyValue u)‖ ≤ _
  refine (convolutionInfinity_norm (r := sourceExponent) _ _).trans ?_
  rw [cutoffKernel_norm]
  exact (mul_le_mul_of_nonneg_left (energyValue_le_pureGradient hSob u)
    (mul_nonneg (cutoffYoungConstant_nonneg q) (Real.sqrt_nonneg M))).trans_eq (by ring)

/-- Actual weak derivatives of the smooth lowpass, represented by the same L2 gradients. -/
theorem low_actual_weak_derivative (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState)
    (j : Fin 3) :
    LineDeriv.lineDerivOp (coordinate j) (Lp.toTemperedDistribution (lowInfinityCLM q hM u)) =
      Lp.toTemperedDistribution (lowL2 q M (energyGradient j u)) := by
  change LineDeriv.lineDerivOp (coordinate j)
    (Lp.toTemperedDistribution (convolutionInfinity (r := sourceExponent)
      (cutoffKernel q hM) (energyValue u))) = _
  rw [low_convolution_same_distribution]
  exact (energyDistribution_derivative (lowEnergyState hDensity hSob q hM u) j).trans
    (congrArg (fun f : L2 => Lp.toTemperedDistribution f)
      (lowEnergyState_gradient hDensity hSob q hM u j))

theorem annularInfinity_gradient_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    ‖Paper121Annular.annularInfinityCLM hDensity hSob q hM u‖ ≤
      (10*cutoffL2Constant q)*Real.sqrt M*pureGradientNorm u := by
  have h0 : 0 ≤ (10*cutoffL2Constant q)*Real.sqrt M*pureGradientNorm u :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (cutoffL2Constant_nonneg q))
      (Real.sqrt_nonneg M)) (pureGradientNorm_nonneg u)
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  apply ENNReal.toReal_le_of_le_ofReal h0
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [convolutionInfinity_coe (r := 2)
    (Paper121Annular.enlargedAnnularKernel q hM)
    (Paper121Annular.annularValueL2CLM hDensity hSob q hM u)] with x hx
  change ‖convolutionInfinity (r := 2) (Paper121Annular.enlargedAnnularKernel q hM)
    (Paper121Annular.annularValueL2CLM hDensity hSob q hM u) x‖ ≤ _
  rw [hx, ← Paper121Annular.annular_C0_apply]
  exact Paper121Annular.annular_C0_gradient_bound hDensity hSob q hM u x

end HartreeF.Paper121CutoffMaps
