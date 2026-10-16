import FAnnularL1Realization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.AnnularL1
open EnergySpace EnergySpace.Highpass YoungSource MassRecovery

def enlargedAnnular (q : Cutoff) (L : ℝ) : TD →L[ℂ] TD := low q (2 * L) - low q (L / 4)

theorem enlargedAnnular_eq_sum (q : Cutoff) (L : ℝ) (T : TD) :
    enlargedAnnular q L T = annular q (2 * L) T + annular q L T + annular q (L / 2) T := by
  have h₁ : 2 * L / 2 = L := by ring
  have h₂ : L / 2 / 2 = L / 4 := by ring
  simp only [enlargedAnnular, annular, sub_apply, h₁, h₂]
  abel

theorem enlargedAnnular_multiplier (q : Cutoff) {L : ℝ} (hL : 0 < L) (T : TD) :
    enlargedAnnular q L T =
      TemperedDistribution.fourierMultiplierCLM ℂ (enlargedAnnularSymbol q L) T := by
  change 𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (lowSymbol q (2 * L)) (𝓕 T)) -
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (lowSymbol q (L / 4)) (𝓕 T)) =
    𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ (lowSymbol q (2 * L) - lowSymbol q (L / 4)) (𝓕 T))
  rw [TemperedDistribution.smulLeftCLM_sub (lowSymbol_temperate q (by positivity))
    (lowSymbol_temperate q (by positivity)), sub_apply]
  exact (map_sub (fourierInvCLM ℂ TD) _ _).symm

theorem enlargedAnnularSymbol_temperate (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    (enlargedAnnularSymbol q L).HasTemperateGrowth :=
  (lowSymbol_temperate q (by positivity : 0 < 2 * L)).sub
    (lowSymbol_temperate q (by positivity : 0 < L / 4))

/-- Only the enlarged band absorbs the standard band; no smooth cutoff is asserted idempotent. -/
theorem annular_enlargedAnnular (q : Cutoff) {L : ℝ} (hL : 0 < L) (T : TD) :
    annular q L (enlargedAnnular q L T) = annular q L T := by
  rw [annular_multiplier q hL, enlargedAnnular_multiplier q hL,
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (enlargedAnnularSymbol_temperate q hL) (annularSymbol_temperate q hL),
    annular_multiplier q hL]
  congr 2
  funext ξ
  exact (mul_comm _ _).trans (annularSymbol_mul_enlarged q hL ξ)

/-- The enlarged-band representative is a literal sum of three constructed L1 classes. -/
def enlargedAnnularL1Value (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (H : Fin 3 → OneSpace) : OneSpace :=
  annularL1Value q (by positivity : 0 < 2 * L) H + annularL1Value q hL H +
    annularL1Value q (by positivity : 0 < L / 2) H

theorem enlargedAnnularL1Value_distribution (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (T : TD) (H : Fin 3 → OneSpace)
    (hH : ∀ j : Fin 3, ∂_{coordinate j} T = Lp.toTemperedDistribution (H j)) :
    Lp.toTemperedDistribution (enlargedAnnularL1Value q hL H) = enlargedAnnular q L T := by
  change (Lp.toTemperedDistributionCLM ℂ volume 1) _ = _
  unfold enlargedAnnularL1Value
  rw [map_add, map_add]
  simp only [Lp.toTemperedDistributionCLM_apply, annularL1Value_distribution q _ T H hH]
  exact (enlargedAnnular_eq_sum q L T).symm

theorem enlargedAnnularL1Value_norm (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (H : Fin 3 → OneSpace) :
    ‖enlargedAnnularL1Value q hL H‖ ≤
      ((7 / 2 : ℝ) * annularConstant q / L) * ∑ j : Fin 3, ‖H j‖ := by
  calc
    _ ≤ ‖annularL1Value q (by positivity : 0 < 2 * L) H‖ +
        ‖annularL1Value q hL H‖ + ‖annularL1Value q (by positivity : 0 < L / 2) H‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (annularConstant q / (2 * L)) * (∑ j : Fin 3, ‖H j‖) +
        (annularConstant q / L) * (∑ j : Fin 3, ‖H j‖) +
        (annularConstant q / (L / 2)) * (∑ j : Fin 3, ‖H j‖) := by
      exact add_le_add (add_le_add (annularL1Value_norm q (by positivity) H)
        (annularL1Value_norm q hL H)) (annularL1Value_norm q (by positivity) H)
    _ = _ := by ring

end HartreeF.AnnularL1
