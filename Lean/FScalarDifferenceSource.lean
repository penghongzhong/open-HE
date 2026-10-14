import FScalarSourceRepresentatives

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.LocalScalarSource
open EnergySpace ForcingDomain TimeHolder

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    (mu : Measure T) [IsFiniteMeasure mu]

theorem represented_difference_mixedNorm {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u v : C(T, EnergyState)) (f g : T → Space → ℂ)
    (hf : ∀ᵐ t ∂mu, f t =ᵐ[volume] energyValue (u t))
    (hg : ∀ᵐ t ∂mu, g t =ᵐ[volume] energyValue (v t)) :
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => forcing alpha c (f t) x - forcing alpha c (g t) x) =
        ‖scalarSource mu hH u - scalarSource mu hH v‖ₑ := by
  rw [← forcingDifference_mixedNorm_eq mu hH u v]
  apply eLpNorm_congr_ae
  filter_upwards [hf, hg] with t hft hgt
  apply eLpNorm_congr_ae
  exact (forcing_ae_of_ae (alpha := alpha) (c := c) hft).sub
    (forcing_ae_of_ae (alpha := alpha) (c := c) hgt)

theorem represented_difference_mixedNorm_ne_top {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u v : C(T, EnergyState)) (f g : T → Space → ℂ)
    (hf : ∀ᵐ t ∂mu, f t =ᵐ[volume] energyValue (u t))
    (hg : ∀ᵐ t ∂mu, g t =ᵐ[volume] energyValue (v t)) :
    mixedNorm mu volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => forcing alpha c (f t) x - forcing alpha c (g t) x) ≠ ∞ := by
  rw [represented_difference_mixedNorm mu hH u v f g hf hg]
  exact enorm_ne_top

theorem represented_differenceSource_coeFn {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u v : C(T, EnergyState)) (f g : T → Space → ℂ)
    (hf : ∀ᵐ t ∂mu, f t =ᵐ[volume] energyValue (u t))
    (hg : ∀ᵐ t ∂mu, g t =ᵐ[volume] energyValue (v t)) :
    ∀ᵐ t ∂mu, ∀ᵐ x ∂(volume : Measure Space),
      (scalarSource mu hH u - scalarSource mu hH v) t x =
        forcing alpha c (f t) x - forcing alpha c (g t) x := by
  filter_upwards [scalarDifferenceSource_coeFn mu hH u v, hf, hg] with t hs hft hgt
  exact Filter.EventuallyEq.trans hs
    ((forcing_ae_of_ae (alpha := alpha) (c := c) hft).sub
      (forcing_ae_of_ae (alpha := alpha) (c := c) hgt)).symm

end HartreeF.LocalScalarSource
