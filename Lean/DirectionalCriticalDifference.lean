import DominatedCriticalNorm
import WeightedSixComparison
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.DerivativeMajorization
open ForcingDomain GradientMajorants

/-- The actual directional candidate satisfies the full spatial critical
six-term difference estimate. Identification with a weak forcing derivative
and time integration remain separate. -/
theorem directional_candidate_critical_difference {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (u v h k : Space → ℂ),
      MemLp u 6 volume → MemLp v 6 volume → MemLp u 10 volume → MemLp v 10 volume →
      MemLp h (ENNReal.ofReal (30/13 : ℝ)) volume →
      MemLp k (ENNReal.ofReal (30/13 : ℝ)) volume →
      MemLp (directionalCandidate α c u h-directionalCandidate α c v k)
        (ENNReal.ofReal (6/5 : ℝ)) volume ∧
      (eLpNorm (directionalCandidate α c u h-directionalCandidate α c v k)
        (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤
        (C : ℝ)*(singleWeight α (sumAmplitude u v) (fun x => ‖h x-k x‖)+
          spacetimeDifferenceWeight α (sumAmplitude u v) (differenceAmplitude u v) (fun x => ‖k x‖)+
          mixedDifferenceWeight α (sumAmplitude u v) (differenceAmplitude u v) (fun x => ‖k x‖)) := by
  obtain ⟨C0,h0⟩ := six_majorant_domain_bound hH
  let C : ℝ≥0 := ⟨(6+α)^2*(C0 : ℝ), mul_nonneg (sq_nonneg _) C0.coe_nonneg⟩
  refine ⟨C,?_⟩
  intro u v h k hu6 hv6 hu10 hv10 hh hk
  have hV (x : Space) : 0≤sumAmplitude u v x := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hW (x : Space) : 0≤differenceAmplitude u v x := norm_nonneg _
  have hY (x : Space) : 0≤‖k x‖ := norm_nonneg _
  have hZ (x : Space) : 0≤‖h x-k x‖ := norm_nonneg _
  obtain ⟨hd,hm,hn⟩ := h0 (sumAmplitude u v) (differenceAmplitude u v)
    (fun x => ‖k x‖) (fun x => ‖h x-k x‖) hV hW (hu6.norm.add hv6.norm)
    (hu10.norm.add hv10.norm) (hu6.sub hv6).norm (hu10.sub hv10).norm hk.norm (hh.sub hk).norm
  have hmeas := (directionalCandidate_measurable α c hu6.aestronglyMeasurable hh.aestronglyMeasurable).sub
    (directionalCandidate_measurable α c hv6.aestronglyMeasurable hk.aestronglyMeasurable)
  have hbound := directional_candidate_six_ae hH.order_pos hH.normalization_pos.le
    hu6.aestronglyMeasurable hv6.aestronglyMeasurable hh.aestronglyMeasurable hk.aestronglyMeasurable hd
  have hb : ∀ᵐ x ∂volume,
      ‖(directionalCandidate α c u h-directionalCandidate α c v k) x‖≤
        (6+α)^2*majorantSum α c (sumAmplitude u v) (differenceAmplitude u v)
          (fun y => ‖k y‖) (fun y => ‖h y-k y‖) x := by
    filter_upwards [hbound] with x hx
    exact hx.trans (weightedMajorantSum_le hH.order_pos hH.normalization_pos.le hV hW hY hZ x)
  obtain ⟨hmem,hest⟩ := dominated_critical_norm hmeas hm (sq_nonneg _)
    (fun x => majorantSum_nonneg hH.normalization_pos.le hV hW hY hZ x) hb
  refine ⟨hmem,?_⟩
  have hCval : (C : ℝ)=(6+α)^2*(C0 : ℝ) := rfl
  exact hest.trans ((mul_le_mul_of_nonneg_left hn (sq_nonneg _)).trans_eq (by rw [hCval]; ring))

#print axioms directional_candidate_critical_difference
end HartreeF.DerivativeMajorization
