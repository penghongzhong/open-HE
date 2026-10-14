import FActualHartreeL2DifferenceTime
import FDirectionalDifferenceQuantitative

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2Difference
open ForcingDomain DerivativeMajorization TimeHolder

/-- The mixed L2 difference estimate expressed solely with the complex input
norms and complex difference norms, for direct use by path-space consumers. -/
theorem actual_forcing_difference_mixed_sum_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
      (u v : T → Space → ℂ),
      AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume) →
      AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (mu.prod volume) →
      (∀ᵐ t ∂mu, MemLp (u t) 6 volume ∧ MemLp (u t) 10 volume) →
      (∀ᵐ t ∂mu, MemLp (v t) 6 volume ∧ MemLp (v t) 10 volume) →
      mixedNorm mu volume 2 2 (fun t => forcing α c (u t)-forcing α c (v t)) ≤
        (C : ℝ≥0∞) *
        ((mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v) ^ (2*α) *
          (mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v) ^ (4 : ℝ) *
          mixedNorm mu volume 10 10 (fun t => u t-v t) +
        (mixedNorm mu volume ∞ 6 u + mixedNorm mu volume ∞ 6 v) ^ (5*α/3) *
          (mixedNorm mu volume 10 10 u + mixedNorm mu volume 10 10 v) ^ (4+α/3) *
          mixedNorm mu volume ∞ 6 (fun t => u t-v t) ^ (α/3) *
          mixedNorm mu volume 10 10 (fun t => u t-v t) ^ (1-α/3)) := by
  obtain ⟨C,hC⟩ := actual_forcing_difference_mixed_bound hH
  refine ⟨C, ?_⟩
  intro T _ mu _ u v hu hv hsu hsv
  have hb := hC mu u v hu hv hsu hsv
  have hd10 : mixedNorm mu volume 10 10 (fun t => differenceAmplitude (u t) (v t)) =
      mixedNorm mu volume 10 10 (fun t => u t-v t) :=
    mixed_norm_norm_eq mu 10 10 (fun t => u t-v t) (hu.sub hv)
  have hd6 : mixedNorm mu volume ∞ 6 (fun t => differenceAmplitude (u t) (v t)) =
      mixedNorm mu volume ∞ 6 (fun t => u t-v t) :=
    mixed_norm_norm_eq mu ∞ 6 (fun t => u t-v t) (hu.sub hv)
  rw [hd10,hd6] at hb
  have hE := sum_amplitude_mixed_le mu ∞ 6 (by norm_num) (by norm_num) (by norm_num) u v hu hv
  have hS := sum_amplitude_mixed_le mu 10 10 (by norm_num) (by norm_num) (by norm_num) u v hu hv
  have ha2 : 0 ≤ 2*α := by linarith [hH.order_pos]
  have ha5 : 0 ≤ 5*α/3 := by linarith [hH.order_pos]
  have ha4 : 0 ≤ 4+α/3 := by linarith [hH.order_pos]
  apply hb.trans
  gcongr

#print axioms actual_forcing_difference_mixed_sum_bound
end HartreeF.ForcingL2Difference
