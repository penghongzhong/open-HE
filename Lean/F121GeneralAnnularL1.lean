import FFourierInverseGradient
import F121GeneralAnnularKernel

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory FourierTransform Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.GeneralAnnular
open EnergySpace YoungSource MassRecovery
open AnnularL1 (inverseGradientL1 inverseGradientL1_distribution inverseGradientL1_norm
  coordinateDerivativeSymbol one_distribution_injective)

/-- The actual general smooth annular Fourier multiplier. -/
def annular (q : Symbol) (L : ℝ) : TD →L[ℂ] TD :=
  TemperedDistribution.fourierMultiplierCLM ℂ (annularSymbol q L)

theorem annular_multiplier (q : Symbol) {L : ℝ} (_hL : 0 < L) (T : TD) :
    annular q L T = TemperedDistribution.fourierMultiplierCLM ℂ (annularSymbol q L) T := rfl

/-- Constructed L1 representative; no L1 representative of the original T is needed. -/
def annularL1Value (q : Symbol) {L : ℝ} (hL : 0 < L) (H : Fin 3 → OneSpace) : OneSpace :=
  inverseGradientL1 (inverseKernel q hL) H

/-- Exact dependence on the fixed cutoff, not an unspecified constant premise. -/
def annularConstant (q : Symbol) : ℝ :=
  ∑ j : Fin 3, ‖(inverseKernel q (by norm_num : 0 < (1 : ℝ)) j).toLp 1 volume‖

theorem annularConstant_nonneg (q : Symbol) : 0 ≤ annularConstant q :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem annularL1Value_distribution (q : Symbol) {L : ℝ} (hL : 0 < L)
    (T : TD) (H : Fin 3 → OneSpace)
    (hH : ∀ j : Fin 3, ∂_{coordinate j} T = Lp.toTemperedDistribution (H j)) :
    Lp.toTemperedDistribution (annularL1Value q hL H) = annular q L T := by
  rw [annular_multiplier q hL]
  apply inverseGradientL1_distribution _ _ _ T H hH
  intro ξ
  simp only [inverseKernel_fourier, inverseSchwartz_apply, coordinateDerivativeSymbol]
  simpa only [mul_comm] using inverseSymbol_reconstruction q L ξ

theorem annularL1Value_norm_weighted (q : Symbol) {L : ℝ} (hL : 0 < L)
    (H : Fin 3 → OneSpace) :
    ‖annularL1Value q hL H‖ ≤ L⁻¹ *
      ∑ j : Fin 3, ‖(inverseKernel q (by norm_num : 0 < (1 : ℝ)) j).toLp 1 volume‖ * ‖H j‖ := by
  calc
    _ ≤ ∑ j : Fin 3, ‖(inverseKernel q hL j).toLp 1 volume‖ * ‖H j‖ :=
      inverseGradientL1_norm _ _
    _ = _ := by
      simp_rw [inverseKernel_norm_one q hL]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem annularL1Value_norm (q : Symbol) {L : ℝ} (hL : 0 < L)
    (H : Fin 3 → OneSpace) :
    ‖annularL1Value q hL H‖ ≤ (annularConstant q / L) * ∑ j : Fin 3, ‖H j‖ := by
  apply (annularL1Value_norm_weighted q hL H).trans
  have hs : (∑ j : Fin 3,
      ‖(inverseKernel q (by norm_num : 0 < (1 : ℝ)) j).toLp 1 volume‖ * ‖H j‖) ≤
      annularConstant q * ∑ j : Fin 3, ‖H j‖ := by
    unfold annularConstant
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun i _ => norm_nonneg (H i)) (Finset.mem_univ j))
      (norm_nonneg _)
  calc
    _ ≤ L⁻¹ * (annularConstant q * ∑ j : Fin 3, ‖H j‖) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Uniqueness includes any independently obtained actual L1 representative. -/
theorem annularL1Value_unique (q : Symbol) {L : ℝ} (hL : 0 < L)
    (T : TD) (H : Fin 3 → OneSpace)
    (hH : ∀ j : Fin 3, ∂_{coordinate j} T = Lp.toTemperedDistribution (H j))
    (v : OneSpace) (hv : Lp.toTemperedDistribution v = annular q L T) :
    v = annularL1Value q hL H := by
  apply one_distribution_injective
  exact hv.trans (annularL1Value_distribution q hL T H hH).symm

end HartreeF.GeneralAnnular
