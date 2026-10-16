import FBoundedHartreeGradientMajorant

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.BoundedHartreeGradient
open ForcingDomain GradientMajorants RieszWeakDerivative WeakHartreeChain WeakHartreeProduct

/-- Actual projected forcing gradients gain L1 with one bounded-value factor.
The higher membership inputs serve only to identify the existing actual gradient field;
the numerical bound uses only L6, L2 gradients and the displayed bounded value. -/
theorem projected_forcing_gradient_L1_smallOrder {α c : ℝ}
    (hH : OrdinaryHLS α c) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℂ →L[ℝ] ℝ), ‖A‖ ≤ 1 →
      ∀ (u : Space → ℂ) (U V : Space → Space) (M : ℝ),
      MemLp u 6 volume → MemLp u 10 volume →
      MemLp U 2 volume → MemLp V 2 volume →
      MemLp U (ENNReal.ofReal (30 / 13 : ℝ)) volume →
      MemLp V (ENNReal.ofReal (30 / 13 : ℝ)) volume →
      0 ≤ M → (∀ᵐ x ∂volume, ‖u x‖ ≤ M) →
      MemLp (potentialProductGradient α c (projectedLocalFactor (1 + α) A) u U V) 1 volume ∧
      (eLpNorm (potentialProductGradient α c (projectedLocalFactor (1 + α) A) u U V) 1 volume).toReal ≤
        C * M * spatialNorm 6 (fun x => ‖u x‖) ^ (3 + 2 * α) *
          spatialNorm 2 (fun x => ‖U x‖ + ‖V x‖) := by
  obtain ⟨C1, hC1⟩ := bounded_majorant1_domain_bound hH
  obtain ⟨C4, hC4⟩ := bounded_majorant4_domain_bound hH hα1
  let C : ℝ := (3 + α) * C4 + (3 * (2 + α)) * C1
  have hα := hH.order_pos
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A hA u U V M hu6 hu10 hU2 hV2 hU hV hM huM
  have hZ : MemLp (fun x => ‖U x‖ + ‖V x‖) 2 volume := hU2.norm.add hV2.norm
  have hn : ∀ x, 0 ≤ ‖u x‖ := fun x => norm_nonneg _
  have hnM : ∀ᵐ x ∂volume, ‖‖u x‖‖ ≤ M := by simpa only [norm_norm] using huM
  obtain ⟨_, h1⟩ := hC1 _ _ M hn hu6.norm hZ hM hnM
  obtain ⟨hd4, h4⟩ := hC4 _ _ M hn hu6.norm hZ hM hnM
  have hb := (spatialBound_const_mul h4 (show 0 ≤ 3 + α by linarith)).add
    (spatialBound_const_mul h1 (show 0 ≤ 3 * (2 + α) by positivity)) (by norm_num)
  have hm := potentialProductGradient_aestronglyMeasurable hH
    (projectedLocalFactor_contDiff_one (by linarith : 1 < 1 + α) A) hu6 hu10 hU hV
  have hr := memLp_one_bound_of_majorant hb hm
    (projected_forcing_gradient_majorant hα hH.normalization_pos.le A hA u U V hd4)
  refine ⟨hr.1, ?_⟩
  convert hr.2 using 1
  dsimp [C]
  ring

end HartreeF.BoundedHartreeGradient
