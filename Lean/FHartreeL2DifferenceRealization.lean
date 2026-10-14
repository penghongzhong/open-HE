import FHartreeL2SourceRealization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2
open TimeHolder

/-- Equality of actual nested L² differences with literal mixed norms.
This bridge is independent of Hartree and uses only two verified representations. -/
theorem represented_l2_difference_enorm {T : Type*} [MeasurableSpace T]
    (mu : Measure T) (F G : Lp (Lp ℂ 2 (volume : Measure Space)) 2 mu)
    (f g : T → Space → ℂ)
    (hf : ∀ᵐ t ∂mu, ∀ᵐ x ∂volume, F t x = f t x)
    (hg : ∀ᵐ t ∂mu, ∀ᵐ x ∂volume, G t x = g t x) :
    ‖F - G‖ₑ = mixedNorm mu volume 2 2 (fun t x => f t x - g t x) := by
  calc
    _ = eLpNorm (F - G) 2 mu := Lp.enorm_def _
    _ = eLpNorm (fun t => ‖(F - G) t‖ₑ) 2 mu :=
      (eLpNorm_enorm _ (Lp.aestronglyMeasurable _)).symm
    _ = _ := by
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub F G, hf, hg] with t ht hft hgt
      rw [ht, Lp.enorm_def]
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub (F t) (G t), hft, hgt] with x hx hfx hgx
      simpa only [Pi.sub_apply, hfx, hgx] using hx

#print axioms represented_l2_difference_enorm
end HartreeF.ForcingL2
