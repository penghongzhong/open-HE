import FAnnularWeakGradientRealization
import FAnnularLpCompatibility

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal
namespace HartreeF.Paper121PureLow
open EnergySpace EnergySpace.Highpass AnnularL1 MassRecovery WeakHartreeProduct

/-- The annular conclusion of Lemma 6.6, conditional on the actual weak
L1 gradient. This component does not yet produce the Hartree gradient. -/
theorem actual_annular_common_representative {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : V → ℂ} {U W : V → V} (hf : MemLp f p volume)
    (hU : MemLp U 1 volume) (hW : MemLp W 1 volume)
    (hwR : HasWeakGradient (fun x => (f x).re) U)
    (hwI : HasWeakGradient (fun x => (f x).im) W)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) :
    let g := annularL1Value q hL (weakGradientOne hU hW)
    Integrable (g : V → ℂ) volume ∧
    MemLp (g : V → ℂ) sourceExponent volume ∧
    Lp.toTemperedDistribution g = annular q L (Lp.toTemperedDistribution (hf.toLp f)) ∧
    ‖g‖ ≤ (annularConstant q / L) * ∑ j : Fin 3, ‖weakGradientOne hU hW j‖ := by
  have h := actual_weak_gradient_annular hf hU hW hwR hwI q hL
  exact ⟨memLp_one_iff_integrable.mp (Lp.memLp _),
    annularL1Value_memLp_six_fifths q hL _, h.1, h.2⟩

end HartreeF.Paper121PureLow
