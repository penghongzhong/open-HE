import FAnnularL1Realization
import FEnergyWeakGradientTemperedDerivative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.AnnularL1
open EnergySpace EnergySpace.Highpass MassRecovery SobolevStretch WeakHartreeProduct

/-- The concrete coordinate L1 classes of the given real and imaginary weak gradients. -/
def weakGradientOne {U W : V → V} (hU : MemLp U 1 volume) (hW : MemLp W 1 volume)
    (j : Fin 3) : OneSpace :=
  (directionalField_memLp hU hW (coordinate j)).toLp
    (directionalField U W (coordinate j))

/-- Actual weak derivatives, without assuming the original function in L1,
produce the same annular distribution and the quantitative L1 representative. -/
theorem actual_weak_gradient_annular {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : V → ℂ} {U W : V → V} (hf : MemLp f p volume)
    (hU : MemLp U 1 volume) (hW : MemLp W 1 volume)
    (hwR : HasWeakGradient (fun x => (f x).re) U)
    (hwI : HasWeakGradient (fun x => (f x).im) W)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    Lp.toTemperedDistribution (annularL1Value q hL (weakGradientOne hU hW)) =
      annular q L (Lp.toTemperedDistribution (hf.toLp f)) ∧
    ‖annularL1Value q hL (weakGradientOne hU hW)‖ ≤
      (annularConstant q / L) * ∑ j : Fin 3, ‖weakGradientOne hU hW j‖ := by
  refine ⟨annularL1Value_distribution q hL _ _ ?_, annularL1Value_norm q hL _⟩
  intro j
  exact weak_gradient_tempered_derivative hf hU hW hwR hwI (coordinate j)

end HartreeF.AnnularL1
