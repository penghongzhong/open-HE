import FCrossContinuityPointwise

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.CrossContinuity
open ForcingDomain WeakHartreeChain DerivativeMajorization GradientMajorants

def valueEnvelope (u U v V : Space → ℂ) : Space → ℝ :=
  sumAmplitude u U + sumAmplitude v V

def differenceEnvelope (u U v V : Space → ℂ) : Space → ℝ :=
  differenceAmplitude u U + differenceAmplitude v V

def referenceEnvelope (H K : Space → ℂ) : Space → ℝ := fun x => ‖H x‖+‖K x‖
def directionEnvelope (h H k K : Space → ℂ) : Space → ℝ := fun x => ‖h x-H x‖+‖k x-K x‖

theorem inner_measurable (α c : ℝ) {u h v : Space → ℂ}
    (hu : AEStronglyMeasurable u volume) (hh : AEStronglyMeasurable h volume)
    (hv : AEStronglyMeasurable v volume) : AEStronglyMeasurable (innerField α c u h v) volume :=
  (rieszConvolution_aestronglyMeasurable α c (directionalDensity_measurable α hu hh)).smul
    (ForcingDomain.localFactor_measurable α hv)

theorem outer_measurable (α c : ℝ) {u v k : Space → ℂ}
    (hu : AEStronglyMeasurable u volume) (hv : AEStronglyMeasurable v volume)
    (hk : AEStronglyMeasurable k volume) : AEStronglyMeasurable (outerField α c u v k) volume :=
  (rieszConvolution_aestronglyMeasurable α c
    ((hu.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable)).smul
    (localFactorDerivative_action_measurable (1+α) hv hk)

/-- Separate literal spatial norm bounds. The real envelopes are only HLS input
functions; no Sobolev gradient or solution structure is asserted for them. -/
theorem cross_pair_spatial_bound {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (u U h H v V k K : Space → ℂ),
      MemLp u 6 volume → MemLp U 6 volume → MemLp v 6 volume → MemLp V 6 volume →
      MemLp u 10 volume → MemLp U 10 volume → MemLp v 10 volume → MemLp V 10 volume →
      MemLp h (ENNReal.ofReal (30/13 : ℝ)) volume → MemLp H (ENNReal.ofReal (30/13 : ℝ)) volume →
      MemLp k (ENNReal.ofReal (30/13 : ℝ)) volume → MemLp K (ENNReal.ofReal (30/13 : ℝ)) volume →
      let A := valueEnvelope u U v V
      let B := differenceEnvelope u U v V
      let Y := referenceEnvelope H K
      let Z := directionEnvelope h H k K
      let R := (C : ℝ)*(singleWeight α A Z+spacetimeDifferenceWeight α A B Y+mixedDifferenceWeight α A B Y)
      (MemLp (innerField α c u h v-innerField α c U H V) (ENNReal.ofReal (6/5 : ℝ)) volume ∧
       (eLpNorm (innerField α c u h v-innerField α c U H V) (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤ R) ∧
      (MemLp (outerField α c u v k-outerField α c U V K) (ENNReal.ofReal (6/5 : ℝ)) volume ∧
       (eLpNorm (outerField α c u v k-outerField α c U V K) (ENNReal.ofReal (6/5 : ℝ)) volume).toReal ≤ R) := by
  obtain ⟨C0,h0⟩ := six_majorant_domain_bound hHLS
  let C : ℝ≥0 := ⟨(6+α)^2*(C0 : ℝ),mul_nonneg (sq_nonneg _) C0.coe_nonneg⟩
  refine ⟨C,?_⟩
  intro u U h H v V k K hu6 hU6 hv6 hV6 hu10 hU10 hv10 hV10 hh hH hk hK
  dsimp only
  let A := valueEnvelope u U v V
  let B := differenceEnvelope u U v V
  let Y := referenceEnvelope H K
  let Z := directionEnvelope h H k K
  have hA (x : Space) : 0≤A x := by dsimp [A,valueEnvelope,sumAmplitude]; positivity
  have hB (x : Space) : 0≤B x := by dsimp [B,differenceEnvelope,differenceAmplitude]; positivity
  have hY (x : Space) : 0≤Y x := by dsimp [Y,referenceEnvelope]; positivity
  have hZ (x : Space) : 0≤Z x := by dsimp [Z,directionEnvelope]; positivity
  have hA6 : MemLp A 6 volume := (hu6.norm.add hU6.norm).add (hv6.norm.add hV6.norm)
  have hA10 : MemLp A 10 volume := (hu10.norm.add hU10.norm).add (hv10.norm.add hV10.norm)
  have hB6 : MemLp B 6 volume := (hu6.sub hU6).norm.add (hv6.sub hV6).norm
  have hB10 : MemLp B 10 volume := (hu10.sub hU10).norm.add (hv10.sub hV10).norm
  have hYm : MemLp Y (ENNReal.ofReal (30/13 : ℝ)) volume := hH.norm.add hK.norm
  have hZm : MemLp Z (ENNReal.ofReal (30/13 : ℝ)) volume := (hh.sub hH).norm.add (hk.sub hK).norm
  obtain ⟨hd,hm,hn⟩ := h0 A B Y Z hA hB hA6 hA10 hB6 hB10 hYm hZm
  have hb := cross_pair_ae hHLS.order_pos hHLS.normalization_pos.le
    hu6.aestronglyMeasurable hU6.aestronglyMeasurable hh.aestronglyMeasurable hH.aestronglyMeasurable
    (show ∀ x, sumAmplitude u U x ≤ A x from fun x => le_add_of_nonneg_right (by dsimp [sumAmplitude]; positivity))
    (show ∀ x, differenceAmplitude u U x ≤ B x from fun x => le_add_of_nonneg_right (norm_nonneg _))
    (show ∀ x, ‖H x‖ ≤ Y x from fun x => le_add_of_nonneg_right (norm_nonneg _))
    (show ∀ x, ‖h x-H x‖ ≤ Z x from fun x => le_add_of_nonneg_right (norm_nonneg _))
    (show ∀ x, sumAmplitude v V x ≤ A x from fun x => le_add_of_nonneg_left (by dsimp [sumAmplitude]; positivity))
    (show ∀ x, differenceAmplitude v V x ≤ B x from fun x => le_add_of_nonneg_left (norm_nonneg _))
    (show ∀ x, ‖K x‖ ≤ Y x from fun x => le_add_of_nonneg_left (norm_nonneg _))
    (show ∀ x, ‖k x-K x‖ ≤ Z x from fun x => le_add_of_nonneg_left (norm_nonneg _)) hd
  have hiMeas := (inner_measurable α c hu6.aestronglyMeasurable hh.aestronglyMeasurable hv6.aestronglyMeasurable).sub
    (inner_measurable α c hU6.aestronglyMeasurable hH.aestronglyMeasurable hV6.aestronglyMeasurable)
  have hoMeas := (outer_measurable α c hu6.aestronglyMeasurable hv6.aestronglyMeasurable hk.aestronglyMeasurable).sub
    (outer_measurable α c hU6.aestronglyMeasurable hV6.aestronglyMeasurable hK.aestronglyMeasurable)
  have hnMaj := fun x => majorantSum_nonneg (α := α) hHLS.normalization_pos.le hA hB hY hZ x
  obtain ⟨him,hin⟩ := dominated_critical_norm hiMeas hm (sq_nonneg (6+α)) hnMaj (hb.mono fun _ hx => hx.1)
  obtain ⟨hom,hon⟩ := dominated_critical_norm hoMeas hm (sq_nonneg (6+α)) hnMaj (hb.mono fun _ hx => hx.2)
  have hCval : (C : ℝ)=(6+α)^2*(C0 : ℝ) := rfl
  have hend : (6+α)^2*spatialNorm (6/5) (majorantSum α c A B Y Z) ≤
      (C : ℝ)*(singleWeight α A Z+spacetimeDifferenceWeight α A B Y+mixedDifferenceWeight α A B Y) :=
    (mul_le_mul_of_nonneg_left hn (sq_nonneg _)).trans_eq (by rw [hCval]; ring)
  exact ⟨⟨him,hin.trans hend⟩,⟨hom,hon.trans hend⟩⟩

#print axioms cross_pair_spatial_bound
end HartreeF.CrossContinuity
