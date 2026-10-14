import FActualHartreeL2DifferenceInputs
import FHartreeL2Budget

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2
open ForcingDomain TimeHolder ForcingL2Difference
universe uTime
variable {T : Type uTime} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]

theorem forcing_l2_bound_fixed_measure {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ u : T → Space → ℂ,
      AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume) →
      (∀ᵐ t ∂mu, MemLp (u t) 6 volume ∧ MemLp (u t) 10 volume) →
      mixedNorm mu volume 2 2 (fun t => forcing alpha c (u t)) ≤
        (C : ℝ≥0∞) * mixedNorm mu volume ∞ 6 u ^ (2 * alpha) *
          mixedNorm mu volume 10 10 u ^ (5 : ℝ) := by
  refine (forcing_l2_mixed_bound.{uTime} hH).imp ?_
  intro C hC
  exact @hC T inferInstance mu inferInstance

theorem forcing_l2_difference_bound_fixed_measure {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ u v : T → Space → ℂ,
      AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume) →
      AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume) →
      (∀ᵐ t ∂mu, MemLp (u t) 6 volume ∧ MemLp (u t) 10 volume) →
      (∀ᵐ t ∂mu, MemLp (v t) 6 volume ∧ MemLp (v t) 10 volume) →
      mixedNorm mu volume 2 2 (fun t => forcing alpha c (u t) - forcing alpha c (v t)) ≤
        (C : ℝ≥0∞) * forcingBudget alpha
          (mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v)
          (mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v)
          (mixedNorm mu volume ∞ 6 (fun t => u t - v t))
          (mixedNorm mu volume 10 10 (fun t => u t - v t)) := by
  refine (actual_forcing_difference_mixed_sum_bound.{uTime} hH).imp ?_
  intro C hC
  exact @hC T inferInstance mu inferInstance

#print axioms forcing_l2_bound_fixed_measure
#print axioms forcing_l2_difference_bound_fixed_measure
end HartreeF.ForcingL2
