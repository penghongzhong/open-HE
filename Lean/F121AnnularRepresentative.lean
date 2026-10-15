import F121AnnularL2
import F121ConvolutionC0

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap ZeroAtInfty
namespace HartreeF.Paper121Annular
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open PhysicalLowpass YoungSource Paper121ConvolutionC0

/-- The actual kernel of Q_M, with the original angular-frequency convention. -/
def enlargedAnnularKernel (q : Cutoff) {M : ℝ} (hM : 0 < M) : Test :=
  cutoffKernel q (by linarith : 0 < 2*M) - cutoffKernel q (by linarith : 0 < M/4)

theorem enlargedAnnularKernel_fourier (q : Cutoff) {M : ℝ} (hM : 0 < M) :
    (𝓕 (enlargedAnnularKernel q hM) : V → ℂ) =
      lowSymbol q (2*M)-lowSymbol q (M/4) := by
  have he : 𝓕 (enlargedAnnularKernel q hM) =
      symbolSchwartz q (by linarith : 0 < 2*M)-symbolSchwartz q (by linarith : 0 < M/4) := by
    change (fourierCLM ℂ Test)
      (cutoffKernel q (by linarith : 0 < 2*M)-cutoffKernel q (by linarith : 0 < M/4)) = _
    rw [map_sub]
    exact congrArg₂ (fun f g : Test => f-g) (cutoffKernel_fourier q _)
      (cutoffKernel_fourier q _)
  funext ξ
  exact congrArg (fun f : Test => f ξ) he

theorem enlargedAnnularKernel_l2_bound (q : Cutoff) {M : ℝ} (hM : 0 < M) :
    ‖(enlargedAnnularKernel q hM).toLp 2 volume‖ ≤
      (5*cutoffL2Constant q)*M^(3/2 : ℝ) := by
  have htwo : (2 : ℝ)^(3/2 : ℝ) ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (3/2 : ℝ) ≤ 2)
    norm_num at h
    exact h
  have hA : (2*M)^(3/2 : ℝ) ≤ 4*M^(3/2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hM.le]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hM.le _)
  have hB : (M/4)^(3/2 : ℝ) ≤ M^(3/2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  change ‖(SchwartzMap.toLpCLM ℂ ℂ 2 volume)
    (cutoffKernel q (by linarith : 0 < 2*M)-cutoffKernel q (by linarith : 0 < M/4))‖ ≤ _
  rw [map_sub]
  refine (norm_sub_le _ _).trans ?_
  change ‖(cutoffKernel q (by linarith : 0 < 2*M)).toLp 2 volume‖ +
    ‖(cutoffKernel q (by linarith : 0 < M/4)).toLp 2 volume‖ ≤ _
  rw [cutoffKernel_norm_two, cutoffKernel_norm_two]
  have hc := cutoffL2Constant_nonneg q
  nlinarith [mul_le_mul_of_nonneg_left hA hc, mul_le_mul_of_nonneg_left hB hc]

def annularInfinityCLM (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) : EnergyState →L[ℂ] Lp ℂ ∞ (volume : Measure V) :=
  (convolutionInfinityCLM (p := 2) (r := 2) (enlargedAnnularKernel q hM)).comp
    (annularValueL2CLM hDensity hSob q hM)

def annularC0CLM (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) : EnergyState →L[ℂ] C₀(V, ℂ) :=
  (convolutionC0 (p := 2) (enlargedAnnularKernel q hM)).comp
    (annularValueL2CLM hDensity hSob q hM)

theorem annular_infinity_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    Lp.toTemperedDistribution (annularInfinityCLM hDensity hSob q hM u) =
      low q M (energyDistribution u)-low q (M/2) (energyDistribution u) := by
  change Lp.toTemperedDistribution (convolutionInfinity (r := 2)
    (enlargedAnnularKernel q hM) (annularValueL2CLM hDensity hSob q hM u)) = _
  rw [convolutionInfinity_distribution (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
    enlargedAnnularKernel_fourier, multiplier_sub
      (lowSymbol_temperate q (by linarith : 0 < 2*M))
      (lowSymbol_temperate q (by linarith : 0 < M/4))]
  change (low q (2*M)-low q (M/4))
    (Lp.toTemperedDistribution (annularValueL2CLM hDensity hSob q hM u)) = _
  rw [annular_l2_distribution, annular_distribution_reproduction q hM]

theorem annular_C0_apply (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) (x : V) :
    annularC0CLM hDensity hSob q hM u x =
      convolutionValue (enlargedAnnularKernel q hM) (annularValueL2CLM hDensity hSob q hM u) x :=
  convolutionC0_apply (r := 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) _ _ _

theorem annular_C0_same_L2 (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    (annularC0CLM hDensity hSob q hM u : V → ℂ) =ᵐ[volume]
      annularValueL2CLM hDensity hSob q hM u := by
  have ha := CriticalPathSpace.spatial_ae_eq_of_distribution_eq
    (annularInfinityCLM hDensity hSob q hM u) (annularValueL2CLM hDensity hSob q hM u)
    ((annular_infinity_distribution hDensity hSob q hM u).trans
      (annular_l2_distribution hDensity hSob q hM u).symm)
  have hb := convolutionInfinity_coe (r := 2) (enlargedAnnularKernel q hM)
    (annularValueL2CLM hDensity hSob q hM u)
  have he : convolutionValue (enlargedAnnularKernel q hM)
      (annularValueL2CLM hDensity hSob q hM u) = (annularC0CLM hDensity hSob q hM u : V → ℂ) :=
    (funext (annular_C0_apply hDensity hSob q hM u)).symm
  rw [he] at hb
  exact hb.symm.trans ha

theorem annular_C0_gradient_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) (x : V) :
    ‖annularC0CLM hDensity hSob q hM u x‖ ≤
      (10*cutoffL2Constant q)*Real.sqrt M*pureGradientNorm u := by
  rw [annular_C0_apply]
  have hp : M^(3/2 : ℝ)*M⁻¹ = Real.sqrt M := by
    rw [show (3/2 : ℝ) = 1+(1/2) by norm_num, Real.rpow_add hM, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    field_simp [ne_of_gt hM]
  refine (convolutionValue_norm (r := 2) (enlargedAnnularKernel q hM)
    (annularValueL2CLM hDensity hSob q hM u) x).trans ?_
  calc
    _ ≤ ((5*cutoffL2Constant q)*M^(3/2 : ℝ))*((2*M⁻¹)*pureGradientNorm u) :=
      mul_le_mul (enlargedAnnularKernel_l2_bound q hM)
        (annular_l2_bound hDensity hSob q hM u) (norm_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) (cutoffL2Constant_nonneg q))
          (Real.rpow_nonneg hM.le _))
    _ = (10*cutoffL2Constant q)*(M^(3/2 : ℝ)*M⁻¹)*pureGradientNorm u := by ring
    _ = _ := by rw [hp]

theorem annular_actual_domains (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    MemLp (annularC0CLM hDensity hSob q hM u : V → ℂ) 2 volume ∧
    Continuous (annularC0CLM hDensity hSob q hM u : V → ℂ) ∧
    Tendsto (annularC0CLM hDensity hSob q hM u : V → ℂ) (cocompact V) (𝓝 0) ∧
    (eLpNorm (annularC0CLM hDensity hSob q hM u : V → ℂ) 2 volume).toReal ≤
      (2*M⁻¹)*pureGradientNorm u ∧
    (∀ x : V, ‖annularC0CLM hDensity hSob q hM u x‖ ≤
      (10*cutoffL2Constant q)*Real.sqrt M*pureGradientNorm u) := by
  have he := annular_C0_same_L2 hDensity hSob q hM u
  refine ⟨(Lp.memLp _).congr he.symm, map_continuous _, zero_at_infty _, ?_,
    annular_C0_gradient_bound hDensity hSob q hM u⟩
  rw [eLpNorm_congr_ae he]
  exact annular_l2_bound hDensity hSob q hM u

end HartreeF.Paper121Annular
