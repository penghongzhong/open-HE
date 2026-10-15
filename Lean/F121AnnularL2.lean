import F121CutoffCore

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology
namespace HartreeF.Paper121Annular
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest

theorem multiplier_sub {m n : V → ℂ} (hm : m.HasTemperateGrowth)
    (hn : n.HasTemperateGrowth) (T : TD) :
    TemperedDistribution.fourierMultiplierCLM ℂ (m-n) T =
      TemperedDistribution.fourierMultiplierCLM ℂ m T -
      TemperedDistribution.fourierMultiplierCLM ℂ n T := by
  simp only [TemperedDistribution.fourierMultiplierCLM_apply,
    TemperedDistribution.smulLeftCLM_sub hm hn, sub_apply]
  rfl

theorem nested_low_symbol (q : Cutoff) {M : ℝ} (hM : 0 < M) (ξ : V) :
    lowSymbol q (M/2) ξ * lowSymbol q M ξ = lowSymbol q (M/2) ξ := by
  by_cases h : 2*Real.pi*‖ξ‖ ≤ M
  · rw [lowSymbol_one q hM ξ h, mul_one]
  · rw [lowSymbol_zero q (by linarith : 0 < M/2) ξ (by linarith)]
    simp

theorem nested_low_distribution (q : Cutoff) {M : ℝ} (hM : 0 < M) (T : TD) :
    low q M (low q (M/2) T) = low q (M/2) T := by
  unfold low
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (lowSymbol_temperate q (by linarith : 0 < M/2)) (lowSymbol_temperate q hM)]
  have he : lowSymbol q (M/2)*lowSymbol q M = lowSymbol q (M/2) :=
    funext (nested_low_symbol q hM)
  rw [he]

/-- The actual annular L2 map, with no mass assumption on the input. -/
def annularValueL2CLM (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) : EnergyState →L[ℂ] L2 :=
  (lowL2 q M).comp (highValueL2CLM hDensity hSob q (by linarith : 0 < M/2))

theorem annular_l2_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    Lp.toTemperedDistribution (annularValueL2CLM hDensity hSob q hM u) =
      low q M (energyDistribution u)-low q (M/2) (energyDistribution u) := by
  change Lp.toTemperedDistribution (lowL2 q M
    (highValueL2 hDensity hSob q (by linarith : 0 < M/2) u)) = _
  rw [lowL2_distribution q hM, highValueL2_distribution]
  change low q M (energyDistribution u-low q (M/2) (energyDistribution u)) = _
  rw [map_sub, nested_low_distribution q hM]

theorem annular_l2_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    ‖annularValueL2CLM hDensity hSob q hM u‖ ≤ (2*M⁻¹)*pureGradientNorm u := by
  have h := (lowL2_norm q M
    (highValueL2 hDensity hSob q (by linarith : 0 < M/2) u)).trans
      (highValueL2_bound hDensity hSob q (by linarith : 0 < M/2) u)
  simpa only [inv_div, div_eq_mul_inv] using h

theorem annular_l2_unique (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (q : Cutoff) {M : ℝ} (hM : 0 < M)
    (u : EnergyState) (v : L2)
    (hv : Lp.toTemperedDistribution v =
      low q M (energyDistribution u)-low q (M/2) (energyDistribution u)) :
    v = annularValueL2CLM hDensity hSob q hM u := by
  apply FreeFlow.l2_distribution_injective
  exact hv.trans (annular_l2_distribution hDensity hSob q hM u).symm

theorem annular_distribution_reproduction (q : Cutoff) {M : ℝ} (hM : 0 < M) (T : TD) :
    (low q (2*M)-low q (M/4)) (low q M T-low q (M/2) T) =
      low q M T-low q (M/2) T := by
  have hm := (lowSymbol_temperate q hM).sub
    (lowSymbol_temperate q (by linarith : 0 < M/2))
  have hn := (lowSymbol_temperate q (by linarith : 0 < 2*M)).sub
    (lowSymbol_temperate q (by linarith : 0 < M/4))
  change low q (2*M) (low q M T-low q (M/2) T) -
    low q (M/4) (low q M T-low q (M/2) T) = _
  unfold low
  rw [← multiplier_sub (lowSymbol_temperate q hM)
    (lowSymbol_temperate q (by linarith : 0 < M/2))]
  rw [← multiplier_sub (lowSymbol_temperate q (by linarith : 0 < 2*M))
    (lowSymbol_temperate q (by linarith : 0 < M/4))]
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hm hn]
  have he : (lowSymbol q M-lowSymbol q (M/2))*(lowSymbol q (2*M)-lowSymbol q (M/4)) =
      lowSymbol q M-lowSymbol q (M/2) :=
    funext (Paper121CutoffCore.annular_symbol_reproduction q hM)
  rw [he]

end HartreeF.Paper121Annular
