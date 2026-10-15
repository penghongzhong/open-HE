import F121AffineWeakEscape
import FLinearProfileFrame

/-! R8.4 Lemma 5.6: all three weak-disappearance clauses for the actual
gradients of inverse-normalized EnergyState data. Together with
F121ArbitraryLocalProperness this covers the two assertions of the lemma. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.Paper121WeakDisappearance
open EnergySpace CriticalAffine ProfileEnergy Paper121WeakEscape

theorem weak_disappearance (f : EnergyState)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (y : ℕ → Space) :
    (Tendsto r atTop atTop →
      GradientWeakLimit (fun n => (criticalAffineState (r n) (hr n) (y n)).symm f) 0) ∧
    (Tendsto r atTop (𝓝 0) →
      GradientWeakLimit (fun n => (criticalAffineState (r n) (hr n) (y n)).symm f) 0) ∧
    (∀ A : ℝ, (∀ n, r n ≤ A) → Tendsto (fun n => ‖y n‖) atTop atTop →
      GradientWeakLimit (fun n => (criticalAffineState (r n) (hr n) (y n)).symm f) 0) := by
  constructor
  · intro h j v
    simpa only [criticalAffineState_symm_eq_affineState, energyGradient_affineState,
      map_zero, inner_zero_left] using
      pairing_tendsto_zero_of_scale_infty r hr y h (energyGradient j f) v
  · constructor
    · intro h j v
      simpa only [criticalAffineState_symm_eq_affineState, energyGradient_affineState,
        map_zero, inner_zero_left] using
        pairing_tendsto_zero_of_scale_zero r hr y h (energyGradient j f) v
    · intro A hbound h j v
      simpa only [criticalAffineState_symm_eq_affineState, energyGradient_affineState,
        map_zero, inner_zero_left] using
        pairing_tendsto_zero_of_center_infty r hr y hbound h (energyGradient j f) v

end HartreeF.Paper121WeakDisappearance
