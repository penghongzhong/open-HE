import FTimeNormLocalization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.TimeHolder
open MeasureTheory
open scoped ENNReal NNReal

/-- A smaller time ball has no larger mixed norm. -/
theorem mixedNorm_ball_mono {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (mu : Measure ℝ) (nu : Measure X) (p q : ℝ≥0∞) (f : ℝ → X → E)
    (t0 : ℝ) {r R : ℝ} (hrR : r ≤ R) :
    mixedNorm (mu.restrict (Metric.ball t0 r)) nu p q f ≤
      mixedNorm (mu.restrict (Metric.ball t0 R)) nu p q f :=
  eLpNorm_mono_measure _ (mu.restrict_mono_set (Metric.ball_subset_ball hrR))

/-- Four finite L10 time inputs admit one common positive radius making both
pair sums small. The two codomains and the two spatial exponents may differ,
so this applies to complex fields u,v and real-vector gradient fields P,Q. -/
theorem finite_four_mixedNorm_exists_small_ball {X E G : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedAddCommGroup G]
    (mu : Measure ℝ) (hmu : mu ≤ volume) (nu : Measure X) (q qG : ℝ≥0∞)
    (u v : ℝ → X → E) (P Q : ℝ → X → G)
    (hu : mixedNorm mu nu 10 q u ≠ ∞) (hv : mixedNorm mu nu 10 q v ≠ ∞)
    (hP : mixedNorm mu nu 10 qG P ≠ ∞) (hQ : mixedNorm mu nu 10 qG Q ≠ ∞)
    (t0 eta : ℝ) (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧
      mixedNorm (mu.restrict (Metric.ball t0 r)) nu 10 q u +
        mixedNorm (mu.restrict (Metric.ball t0 r)) nu 10 q v ≤ ENNReal.ofReal eta ∧
      mixedNorm (mu.restrict (Metric.ball t0 r)) nu 10 qG P +
        mixedNorm (mu.restrict (Metric.ball t0 r)) nu 10 qG Q ≤ ENNReal.ofReal eta := by
  have he : 0 < ENNReal.ofReal (eta / 2) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨ru, hru, huSmall⟩ := finite_mixedNorm_exists_small_ball mu hmu nu 10 q
    (by norm_num) (by norm_num) u hu t0 _ he
  obtain ⟨rv, hrv, hvSmall⟩ := finite_mixedNorm_exists_small_ball mu hmu nu 10 q
    (by norm_num) (by norm_num) v hv t0 _ he
  obtain ⟨rP, hrP, hPSmall⟩ := finite_mixedNorm_exists_small_ball mu hmu nu 10 qG
    (by norm_num) (by norm_num) P hP t0 _ he
  obtain ⟨rQ, hrQ, hQSmall⟩ := finite_mixedNorm_exists_small_ball mu hmu nu 10 qG
    (by norm_num) (by norm_num) Q hQ t0 _ he
  let r := min (min ru rv) (min rP rQ)
  have hr : 0 < r := lt_min (lt_min hru hrv) (lt_min hrP hrQ)
  have hru' : r ≤ ru := (min_le_left _ _).trans (min_le_left _ _)
  have hrv' : r ≤ rv := (min_le_left _ _).trans (min_le_right _ _)
  have hrP' : r ≤ rP := (min_le_right _ _).trans (min_le_left _ _)
  have hrQ' : r ≤ rQ := (min_le_right _ _).trans (min_le_right _ _)
  have hhalf : ENNReal.ofReal (eta / 2) + ENNReal.ofReal (eta / 2) = ENNReal.ofReal eta := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  refine ⟨r, hr, ?_, ?_⟩
  · exact (add_le_add ((mixedNorm_ball_mono mu nu 10 q u t0 hru').trans huSmall)
      ((mixedNorm_ball_mono mu nu 10 q v t0 hrv').trans hvSmall)).trans_eq hhalf
  · exact (add_le_add ((mixedNorm_ball_mono mu nu 10 qG P t0 hrP').trans hPSmall)
      ((mixedNorm_ball_mono mu nu 10 qG Q t0 hrQ').trans hQSmall)).trans_eq hhalf

/-- The L∞ time background pair remains below its original cap after time
restriction. This statement has no smallness claim for an L∞ norm. -/
theorem mixedNorm_background_pair_restrict_le {T X E : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [NormedAddCommGroup E]
    (mu : Measure T) (nu : Measure X) (q : ℝ≥0∞) (u v : T → X → E)
    (B : ℝ≥0∞) (hB : mixedNorm mu nu ∞ q u + mixedNorm mu nu ∞ q v ≤ B)
    (s : Set T) :
    mixedNorm (mu.restrict s) nu ∞ q u + mixedNorm (mu.restrict s) nu ∞ q v ≤ B :=
  (add_le_add (mixedNorm_restrict_le mu nu ∞ q u s)
    (mixedNorm_restrict_le mu nu ∞ q v s)).trans hB

/-- The four finite input norms also furnish the required almost-everywhere
spatial membership after every time restriction. -/
theorem finite_four_mixedNorm_restrict_slice_memLp {X E G : Type*}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedAddCommGroup G]
    (mu : Measure ℝ) (nu : Measure X) (q qG : ℝ≥0∞)
    (u v : ℝ → X → E) (P Q : ℝ → X → G)
    (hu : mixedNorm mu nu 10 q u ≠ ∞) (hv : mixedNorm mu nu 10 q v ≠ ∞)
    (hP : mixedNorm mu nu 10 qG P ≠ ∞) (hQ : mixedNorm mu nu 10 qG Q ≠ ∞)
    (s : Set ℝ) :
    ∀ᵐ t ∂mu.restrict s,
      MemLp (u t) q nu ∧ MemLp (v t) q nu ∧ MemLp (P t) qG nu ∧ MemLp (Q t) qG nu := by
  have hau := finite_mixedNorm_ae_slice_memLp mu nu 10 q (by norm_num) (by norm_num) u hu
  have hav := finite_mixedNorm_ae_slice_memLp mu nu 10 q (by norm_num) (by norm_num) v hv
  have haP := finite_mixedNorm_ae_slice_memLp mu nu 10 qG (by norm_num) (by norm_num) P hP
  have haQ := finite_mixedNorm_ae_slice_memLp mu nu 10 qG (by norm_num) (by norm_num) Q hQ
  exact (hau.and (hav.and (haP.and haQ))).filter_mono ae_restrict_le

end HartreeF.TimeHolder
