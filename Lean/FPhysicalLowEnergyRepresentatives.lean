import FPhysicalCutoffKernelBounds
import FHighpassContraction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.PhysicalLowpass
open EnergySpace EnergySpace.Highpass YoungSource SobolevStretch StationarySelfTest

/-- The literal physical lowpass of the original homogeneous state's actual L6 value. -/
def lowPhysical (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) : V → ℂ :=
  convolutionValue (cutoffKernel q hL) (energyValue u)

def lowPhysicalInfinity (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    Lp ℂ ∞ (volume : Measure V) :=
  convolutionInfinity (r := sourceExponent) (cutoffKernel q hL) (energyValue u)

def lowPhysicalInfinityCLM (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    EnergyState →L[ℂ] Lp ℂ ∞ (volume : Measure V) :=
  (convolutionInfinityCLM (r := sourceExponent) (cutoffKernel q hL)).comp energyValue

theorem lowPhysicalInfinityCLM_apply (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    lowPhysicalInfinityCLM q hL u = lowPhysicalInfinity q hL u := rfl

theorem continuousOn_lowPhysicalInfinity {T : Type*} [TopologicalSpace T]
    {u : T → EnergyState} {S : Set T} (hu : ContinuousOn u S)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    ContinuousOn (fun t => lowPhysicalInfinity q hL (u t)) S :=
  (lowPhysicalInfinityCLM q hL).continuous.comp_continuousOn hu

theorem lowPhysical_integrable (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (x : V) :
    Integrable (fun y : V => energyValue u y * cutoffKernel q hL (x - y)) volume :=
  convolutionValue_integrable (r := sourceExponent) _ _ _

theorem lowPhysical_bound (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) (x : V) :
    ‖lowPhysical q hL u x‖ ≤ cutoffYoungConstant q * Real.sqrt L * ‖energyValue u‖ :=
  cutoff_convolution_six_bound q hL _ x

theorem lowPhysical_pureGradient_bound {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) (x : V) :
    ‖lowPhysical q hL u x‖ ≤
      (cutoffYoungConstant q * Real.sqrt L * K ^ ((6 : ℝ)⁻¹)) * pureGradientNorm u := by
  calc
    _ ≤ cutoffYoungConstant q * Real.sqrt L * ‖energyValue u‖ := lowPhysical_bound q hL u x
    _ ≤ cutoffYoungConstant q * Real.sqrt L * (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u) :=
      mul_le_mul_of_nonneg_left (energyValue_le_pureGradient hSob u)
        (mul_nonneg (cutoffYoungConstant_nonneg q) (Real.sqrt_nonneg L))
    _ = _ := by ring

theorem lowPhysical_memLp_top (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    MemLp (lowPhysical q hL u) ∞ volume :=
  convolutionValue_memLp_top (r := sourceExponent) _ _

theorem lowPhysicalInfinity_coe (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    (lowPhysicalInfinity q hL u : V → ℂ) =ᵐ[volume] lowPhysical q hL u :=
  convolutionInfinity_coe (r := sourceExponent) _ _

theorem lowPhysicalInfinity_distribution (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    Lp.toTemperedDistribution (lowPhysicalInfinity q hL u) = low q L (energyDistribution u) :=
  cutoff_convolution_distribution (r := sourceExponent) (by norm_num) q hL (energyValue u)

/-- The actual physical convolution is the SAME original lowEnergyState L6 representative. -/
theorem lowPhysical_same_value (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    lowPhysical q hL u =ᵐ[volume] energyValue (lowEnergyState hDensity hSob q hL u) := by
  have he := CriticalPathSpace.spatial_ae_eq_of_distribution_eq
    (lowPhysicalInfinity q hL u) (energyValue (lowEnergyState hDensity hSob q hL u))
    ((lowPhysicalInfinity_distribution q hL u).trans
      (lowEnergyState_distribution hDensity hSob q hL u).symm)
  exact (lowPhysicalInfinity_coe q hL u).symm.trans he

theorem lowEnergyState_memLp_top (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    MemLp (energyValue (lowEnergyState hDensity hSob q hL u) : V → ℂ) ∞ volume :=
  (memLp_congr_ae (lowPhysical_same_value hDensity hSob q hL u)).mp (lowPhysical_memLp_top q hL u)

theorem lowEnergyState_linf_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    (eLpNorm (energyValue (lowEnergyState hDensity hSob q hL u) : V → ℂ) ∞ volume).toReal ≤
      cutoffYoungConstant q * Real.sqrt L * ‖energyValue u‖ := by
  apply ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (cutoffYoungConstant_nonneg q) (Real.sqrt_nonneg L)) (norm_nonneg _))
  rw [eLpNorm_exponent_top (lowEnergyState_memLp_top hDensity hSob q hL u).aestronglyMeasurable]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [lowPhysical_same_value hDensity hSob q hL u] with x hx
  rw [← hx]
  exact lowPhysical_bound q hL u x

/-- Each actual original gradient is filtered by the same physical convolution kernel. -/
def lowPhysicalGradient (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState)
    (j : Fin 3) : V → ℂ :=
  convolutionValue (cutoffKernel q hL) (energyGradient j u)

theorem lowPhysicalGradient_integrable (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (j : Fin 3) (x : V) :
    Integrable (fun y : V => energyGradient j u y * cutoffKernel q hL (x - y)) volume :=
  convolutionValue_integrable (r := 2) _ _ _

theorem lowPhysicalGradient_bound (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (j : Fin 3) (x : V) :
    ‖lowPhysicalGradient q hL u j x‖ ≤ cutoffL2Constant q * L ^ (3 / 2 : ℝ) * ‖energyGradient j u‖ :=
  cutoff_convolution_two_bound q hL _ x

theorem lowPhysicalGradient_memLp_top (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (j : Fin 3) : MemLp (lowPhysicalGradient q hL u j) ∞ volume :=
  convolutionValue_memLp_top (r := 2) _ _

theorem lowPhysicalGradient_same_gradient (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (j : Fin 3) :
    lowPhysicalGradient q hL u j =ᵐ[volume]
      energyGradient j (lowEnergyState hDensity hSob q hL u) := by
  rw [lowEnergyState_gradient]
  have he := CriticalPathSpace.spatial_ae_eq_of_distribution_eq
    (convolutionInfinity (r := 2) (cutoffKernel q hL) (energyGradient j u))
    (lowL2 q L (energyGradient j u))
    ((cutoff_convolution_distribution (r := 2) (by norm_num) q hL (energyGradient j u)).trans
      (lowL2_distribution q hL (energyGradient j u)).symm)
  exact (convolutionInfinity_coe (r := 2) _ _).symm.trans he

theorem lowEnergyState_gradient_memLp_top (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (u : EnergyState) (j : Fin 3) :
    MemLp (energyGradient j (lowEnergyState hDensity hSob q hL u) : V → ℂ) ∞ volume :=
  (memLp_congr_ae (lowPhysicalGradient_same_gradient hDensity hSob q hL u j)).mp
    (lowPhysicalGradient_memLp_top q hL u j)

theorem lowEnergyState_pureGradient_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {L : ℝ} (hL : 0 < L) (u : EnergyState) :
    pureGradientNorm (lowEnergyState hDensity hSob q hL u) ≤ pureGradientNorm u := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  rw [lowEnergyState_gradient]
  exact pow_le_pow_left₀ (norm_nonneg _) (lowL2_norm q L _) 2

end HartreeF.PhysicalLowpass
