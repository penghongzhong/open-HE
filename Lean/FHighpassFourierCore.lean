import FEnergyFreeProperties
import FCriticalPathSpace
import Mathlib.Tactic.FunProp

/-! Literal D manuscript cutoff and ordinary native L2 Fourier projection.
Only the linear cutoff definitions and proofs are extracted; no D module is imported.
Frequency convention: angular frequency is 2*pi*xi. No highpass realization premise. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap ContDiff
namespace HartreeF.EnergySpace.Highpass
open HartreeF.EnergySpace

/-- Literal smooth radial cutoff of the paper, with its complete domain. -/
structure Cutoff where
  φ : V → ℝ
  smooth : ContDiff ℝ ∞ φ
  radial : ∀ x y : V, ‖x‖ = ‖y‖ → φ x = φ y
  nonneg : ∀ x, 0 ≤ φ x
  le_one : ∀ x, φ x ≤ 1
  eq_one : ∀ x, ‖x‖ ≤ 1 → φ x = 1
  eq_zero : ∀ x, 2 ≤ ‖x‖ → φ x = 0

def lowSymbol (q : Cutoff) (L : ℝ) (ξ : V) : ℂ :=
  (q.φ ((2 * Real.pi / L) • ξ) : ℂ)

def low (q : Cutoff) (L : ℝ) : TD →L[ℂ] TD :=
  TemperedDistribution.fourierMultiplierCLM ℂ (lowSymbol q L)

def high (q : Cutoff) (L : ℝ) : TD →L[ℂ] TD := ContinuousLinearMap.id ℂ TD - low q L

theorem angular_norm (L : ℝ) (hL : 0 < L) (ξ : V) :
    ‖(2 * Real.pi / L) • ξ‖ = (2 * Real.pi * ‖ξ‖) / L := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  ring

theorem lowSymbol_one (q : Cutoff) {L : ℝ} (hL : 0 < L) (ξ : V)
    (h : 2 * Real.pi * ‖ξ‖ ≤ L) : lowSymbol q L ξ = 1 := by
  unfold lowSymbol
  rw [q.eq_one]
  · norm_num
  · rw [angular_norm L hL ξ]
    exact (div_le_one hL).mpr h

theorem lowSymbol_zero (q : Cutoff) {L : ℝ} (hL : 0 < L) (ξ : V)
    (h : 2 * L ≤ 2 * Real.pi * ‖ξ‖) : lowSymbol q L ξ = 0 := by
  unfold lowSymbol
  rw [q.eq_zero]
  · norm_num
  · rw [angular_norm L hL ξ]
    exact (le_div_iff₀ hL).mpr h

theorem lowSymbol_compact (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (lowSymbol q L) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : V) (L / Real.pi))
  intro ξ hξ
  by_contra hn
  have hn' : L / Real.pi < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
  have hz := lowSymbol_zero q hL ξ (by
    have hh := (div_lt_iff₀ Real.pi_pos).mp hn'
    nlinarith)
  exact hξ hz

theorem lowSymbol_temperate (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    (lowSymbol q L).HasTemperateGrowth := by
  apply (lowSymbol_compact q hL).hasTemperateGrowth
  exact Complex.ofRealCLM.contDiff.comp (q.smooth.comp (by fun_prop))

private instance : ENNReal.HolderTriple ∞ 2 2 := ⟨by simp⟩

theorem lowSymbol_norm_le_one (q : Cutoff) (L : ℝ) (ξ : V) : ‖lowSymbol q L ξ‖ ≤ 1 := by
  rw [lowSymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (q.nonneg _)]
  exact q.le_one _

theorem lowSymbol_continuous (q : Cutoff) (L : ℝ) : Continuous (lowSymbol q L) := by
  exact Complex.continuous_ofReal.comp (q.smooth.continuous.comp (by fun_prop))

theorem lowSymbol_memLp (q : Cutoff) (L : ℝ) : MemLp (lowSymbol q L) ∞ (volume : Measure V) :=
  memLp_top_of_bound (lowSymbol_continuous q L).aestronglyMeasurable 1
    (Eventually.of_forall (lowSymbol_norm_le_one q L))

def lowInfinity (q : Cutoff) (L : ℝ) : FreeFlow.LpC ∞ := (lowSymbol_memLp q L).toLp (lowSymbol q L)

def lowMultiply (q : Cutoff) (L : ℝ) : L2 →L[ℂ] L2 := FreeFlow.lpMul ∞ 2 2 (lowInfinity q L)

theorem lowMultiply_coe (q : Cutoff) (L : ℝ) (f : L2) :
    (lowMultiply q L f : V → ℂ) =ᵐ[volume] fun ξ => lowSymbol q L ξ * f ξ := by
  filter_upwards [FreeFlow.lpMul_coe (r := 2) (lowInfinity q L) f, (lowSymbol_memLp q L).coeFn_toLp]
    with ξ h1 h2
  change lowInfinity q L ξ = lowSymbol q L ξ at h2
  exact h1.trans (by rw [h2])

theorem lowMultiply_norm (q : Cutoff) (L : ℝ) (f : L2) : ‖lowMultiply q L f‖ ≤ ‖f‖ := by
  have hh : ‖lowMultiply q L f‖ ≤ 1 * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [lowMultiply_coe q L f] with ξ hξ
    rw [hξ, norm_mul]
    exact mul_le_mul_of_nonneg_right (lowSymbol_norm_le_one q L ξ) (norm_nonneg _)
  simpa only [one_mul] using hh

def lowL2 (q : Cutoff) (L : ℝ) : L2 →L[ℂ] L2 :=
  fourierInvCLM ℂ L2 ∘L lowMultiply q L ∘L fourierCLM ℂ L2

theorem lowL2_fourier (q : Cutoff) (L : ℝ) (f : L2) :
    𝓕 (lowL2 q L f) = lowMultiply q L (𝓕 f) := by
  change 𝓕 (𝓕⁻ (lowMultiply q L (𝓕 f))) = _
  exact fourier_fourierInv_eq _

theorem lowL2_norm (q : Cutoff) (L : ℝ) (f : L2) : ‖lowL2 q L f‖ ≤ ‖f‖ := by
  rw [← Lp.norm_fourier_eq (lowL2 q L f), lowL2_fourier]
  exact (lowMultiply_norm q L (𝓕 f)).trans_eq (Lp.norm_fourier_eq f)

theorem lowMultiply_distribution (q : Cutoff) {L : ℝ} (hL : 0 < L) (f : L2) :
    Lp.toTemperedDistribution (lowMultiply q L f) =
      TemperedDistribution.smulLeftCLM ℂ (lowSymbol q L) (Lp.toTemperedDistribution f) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [lowMultiply_coe q L f] with ξ hξ
  simp only [hξ, SchwartzMap.smulLeftCLM_apply_apply (lowSymbol_temperate q hL), smul_eq_mul]
  ring

theorem lowL2_distribution (q : Cutoff) {L : ℝ} (hL : 0 < L) (f : L2) :
    Lp.toTemperedDistribution (lowL2 q L f) = low q L (Lp.toTemperedDistribution f) := by
  change Lp.toTemperedDistribution (𝓕⁻ (lowMultiply q L (𝓕 f))) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (lowSymbol q L) (𝓕 (Lp.toTemperedDistribution f)))
  rw [← Lp.fourierInv_toTemperedDistribution_eq, lowMultiply_distribution q hL,
    Lp.fourier_toTemperedDistribution_eq]


 theorem derivative_low (q : Cutoff) {L : ℝ} (hL : 0 < L) (T : TD) (v : V) :
    ∂_{v} (low q L T) = low q L (∂_{v} T) := by
  change ∂_{v} (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (lowSymbol q L) (𝓕 T))) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (lowSymbol q L) (𝓕 (∂_{v} T)))
  rw [TemperedDistribution.lineDerivOp_fourierInv_eq,
    TemperedDistribution.fourier_lineDerivOp_eq, map_smul]
  congr 1
  have hi : (fun x : V => (inner ℝ x v : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp (Function.hasTemperateGrowth_inner_left v)
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (lowSymbol_temperate q hL) hi,
    TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hi (lowSymbol_temperate q hL)]
  simp only [mul_comm]

def highL2 (q : Cutoff) (L : ℝ) : L2 →L[ℂ] L2 :=
  ContinuousLinearMap.id ℂ L2 - lowL2 q L

theorem highL2_distribution (q : Cutoff) {L : ℝ} (hL : 0 < L) (f : L2) :
    Lp.toTemperedDistribution (highL2 q L f) = high q L (Lp.toTemperedDistribution f) := by
  change (Lp.toTemperedDistributionCLM ℂ volume 2) (f - lowL2 q L f) = _
  rw [map_sub]
  change Lp.toTemperedDistribution f - Lp.toTemperedDistribution (lowL2 q L f) = _
  rw [lowL2_distribution q hL]
  rfl

theorem highL2_norm (q : Cutoff) (L : ℝ) (f : L2) :
    ‖highL2 q L f‖ ≤ 2 * ‖f‖ := by
  change ‖f - lowL2 q L f‖ ≤ _
  exact (norm_sub_le _ _).trans (by have h := lowL2_norm q L f; linarith)

def highSchwartz (q : Cutoff) (L : ℝ) : Test →L[ℂ] Test :=
  ContinuousLinearMap.id ℂ Test - SchwartzMap.fourierMultiplierCLM ℂ (lowSymbol q L)

theorem highSchwartz_distribution (q : Cutoff) {L : ℝ} (hL : 0 < L) (φ : Test) :
    energyDistribution (schwartzEnergyState (highSchwartz q L φ)) =
      high q L (energyDistribution (schwartzEnergyState φ)) := by
  rw [schwartzEnergyState_distribution, schwartzEnergyState_distribution]
  change (SchwartzMap.toTemperedDistributionCLM V ℂ volume)
    (φ - SchwartzMap.fourierMultiplierCLM ℂ (lowSymbol q L) φ) = _
  rw [map_sub, ← TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (lowSymbol_temperate q hL) φ]
  rfl

theorem highSchwartz_toL2 (q : Cutoff) {L : ℝ} (hL : 0 < L) (φ : Test) :
    (highSchwartz q L φ).toLp 2 volume = highL2 q L (φ.toLp 2 volume) := by
  apply FreeFlow.l2_distribution_injective
  rw [highL2_distribution q hL]
  simp only [Lp.toTemperedDistribution_toLp_eq]
  simpa only [schwartzEnergyState_distribution] using highSchwartz_distribution q hL φ

theorem derivative_high (q : Cutoff) {L : ℝ} (hL : 0 < L) (T : TD) (v : V) :
    ∂_{v} (high q L T) = high q L (∂_{v} T) := by
  change (lineDerivOpCLM ℂ TD v) (T - low q L T) = _
  rw [map_sub]
  change ∂_{v} T - ∂_{v} (low q L T) = _
  rw [derivative_low q hL]
  rfl

theorem highSchwartz_gradient (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (φ : Test) (j : Fin 3) :
    energyGradient j (schwartzEnergyState (highSchwartz q L φ)) =
      highL2 q L (energyGradient j (schwartzEnergyState φ)) := by
  apply FreeFlow.l2_distribution_injective
  rw [highL2_distribution q hL]
  change energyGradientDistribution j (schwartzEnergyState (highSchwartz q L φ)) =
    high q L (energyGradientDistribution j (schwartzEnergyState φ))
  rw [← energyDistribution_derivative, ← energyDistribution_derivative,
    highSchwartz_distribution q hL, derivative_high q hL]

end HartreeF.EnergySpace.Highpass
