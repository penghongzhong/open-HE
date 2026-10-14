import FCrossContinuityEnvelopes

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.CrossContinuity
open ForcingDomain WeakHartreeChain DerivativeMajorization GradientMajorants

/-- A sum of two nonnegative norm differences, with independently labelled
sources and recipients. There is no inference from the norm of their signed sum. -/
theorem cross_pair_pointwise {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {u U h H v V k K : Space → ℂ} {A B Y Z : Space → ℝ}
    (hu : AEStronglyMeasurable u volume) (hU : AEStronglyMeasurable U volume)
    (hh : AEStronglyMeasurable h volume) (hH : AEStronglyMeasurable H volume)
    (hAu : ∀ y, sumAmplitude u U y ≤ A y)
    (hBu : ∀ y, differenceAmplitude u U y ≤ B y)
    (hYh : ∀ y, ‖H y‖ ≤ Y y) (hZh : ∀ y, ‖h y-H y‖ ≤ Z y)
    (hAv : ∀ y, sumAmplitude v V y ≤ A y)
    (hBv : ∀ y, differenceAmplitude v V y ≤ B y)
    (hYk : ∀ y, ‖K y‖ ≤ Y y) (hZk : ∀ y, ‖k y-K y‖ ≤ Z y)
    (x : Space)
    (hd1 : Integrable (fun y => rieszKernel α c (x-y)*A y^(3+α)) volume)
    (hd2 : Integrable (fun y => rieszKernel α c (x-y)*(A y^(2+α)*B y)) volume)
    (hd4 : Integrable (fun y => rieszKernel α c (x-y)*(A y^(2+α)*Z y)) volume)
    (hd5 : Integrable (fun y => rieszKernel α c (x-y)*(A y^(1+α)*B y*Y y)) volume)
    (hd6 : Integrable (fun y => rieszKernel α c (x-y)*(A y^(2+α)*Y y)) volume) :
    ‖innerField α c u h v x-innerField α c U H V x‖+
      ‖outerField α c u v k x-outerField α c U V K x‖ ≤
        weightedMajorantSum α c A B Y Z x := by
  obtain ⟨hP,hPQ⟩ := generalized_potential_envelopes ha hc hu hU hAu hBu x hd1 hd2
  obtain ⟨hE,hDE⟩ := generalized_density_envelopes ha hc hu hU hh hH hAu hBu hYh hZh x hd4 hd5 hd6
  have hnA (y : Space) : 0 ≤ A y := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hAu y)
  have hnB (y : Space) : 0 ≤ B y := (norm_nonneg _).trans (hBu y)
  have hnY (y : Space) : 0 ≤ Y y := (norm_nonneg _).trans (hYh y)
  have hnZ (y : Space) : 0 ≤ Z y := (norm_nonneg _).trans (hZh y)
  have hq : 1<1+α := by linarith
  have hlocal : ‖WeakHartreeChain.localFactor (1+α) (v x)‖ ≤ A x^(2+α) := by
    have ht := localFactor_bound_sum hq (v x) (V x)
    rw [show 1+α+1=2+α by ring] at ht
    exact ht.trans (Real.rpow_le_rpow (by positivity) (hAv x) (by linarith))
  have hlocaldiff : ‖WeakHartreeChain.localFactor (1+α) (v x)-WeakHartreeChain.localFactor (1+α) (V x)‖ ≤
      (2+α)*A x^(1+α)*B x := by
    have ht := localFactor_difference_bound hq (v x) (V x)
    rw [show 1+α+1=2+α by ring] at ht
    apply ht.trans
    dsimp [sumAmplitude,differenceAmplitude] at hAv hBv
    have hAn := hnA x
    have hBn := hnB x
    have hYn := hnY x
    gcongr
    · exact hAv x
    · exact hBv x
  have haction : ‖localFactorDerivative (1+α) (V x) (K x)‖ ≤ (2+α)*A x^(1+α)*Y x := by
    have ht := localFactorDerivative_action_bound_right hq (v x) (V x) (K x)
    rw [show 1+α+1=2+α by ring] at ht
    apply ht.trans
    dsimp [sumAmplitude] at hAv
    have hAn := hnA x
    have hBn := hnB x
    have hYn := hnY x
    gcongr
    · exact hAv x
    · exact hYk x
  have hactiondiff : ‖localFactorDerivative (1+α) (v x) (k x)-localFactorDerivative (1+α) (V x) (K x)‖ ≤
      (2+α)*A x^(1+α)*Z x+((1+α)*(6+α))*A x^α*B x*Y x := by
    have ht := localFactorDerivative_action_difference hq (v x) (V x) (k x) (K x)
    simp only [show 1+α+1=2+α by ring,show 1+α+5=6+α by ring,show 1+α-1=α by ring] at ht
    apply ht.trans
    dsimp [sumAmplitude,differenceAmplitude] at hAv hBv
    have hAn := hnA x
    have hBn := hnB x
    have hYn := hnY x
    gcongr <;> first | exact hAv x | exact hBv x | exact hYk x | exact hZk x
  have hi := (smul_difference_bound_right
    (rieszConvolution α c (directionalDensity α u h) x)
    (rieszConvolution α c (directionalDensity α U H) x)
    (WeakHartreeChain.localFactor (1+α) (v x))
    (WeakHartreeChain.localFactor (1+α) (V x))).trans
      (add_le_add (mul_le_mul hDE hlocal (norm_nonneg _) ((norm_nonneg _).trans hDE))
        (mul_le_mul hE hlocaldiff (norm_nonneg _) ((norm_nonneg _).trans hE)))
  have ho := (smul_difference_bound (potential α c u x) (potential α c U x)
    (localFactorDerivative (1+α) (v x) (k x))
    (localFactorDerivative (1+α) (V x) (K x))).trans
      (add_le_add (mul_le_mul hP hactiondiff (norm_nonneg _) ((norm_nonneg _).trans hP))
        (mul_le_mul hPQ haction (norm_nonneg _) ((norm_nonneg _).trans hPQ)))
  convert add_le_add hi ho using 1
  · rfl
  · dsimp [weightedMajorantSum,majorant1,majorant2,majorant3,majorant4,majorant5,majorant6]
    ring

/-- Both actual cross terms are separately controlled by the literal HLS majorants. -/
theorem cross_pair_ae {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {u U h H v V k K : Space → ℂ} {A B Y Z : Space → ℝ}
    (hu : AEStronglyMeasurable u volume) (hU : AEStronglyMeasurable U volume)
    (hh : AEStronglyMeasurable h volume) (hH : AEStronglyMeasurable H volume)
    (hAu : ∀ y, sumAmplitude u U y ≤ A y) (hBu : ∀ y, differenceAmplitude u U y ≤ B y)
    (hYh : ∀ y, ‖H y‖ ≤ Y y) (hZh : ∀ y, ‖h y-H y‖ ≤ Z y)
    (hAv : ∀ y, sumAmplitude v V y ≤ A y) (hBv : ∀ y, differenceAmplitude v V y ≤ B y)
    (hYk : ∀ y, ‖K y‖ ≤ Y y) (hZk : ∀ y, ‖k y-K y‖ ≤ Z y)
    (hd : MajorantDomains α c A B Y Z) :
    ∀ᵐ x ∂volume,
      ‖innerField α c u h v x-innerField α c U H V x‖ ≤ (6+α)^2*majorantSum α c A B Y Z x ∧
      ‖outerField α c u v k x-outerField α c U V K x‖ ≤ (6+α)^2*majorantSum α c A B Y Z x := by
  have hnA (y : Space) : 0 ≤ A y := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hAu y)
  have hnB (y : Space) : 0 ≤ B y := (norm_nonneg _).trans (hBu y)
  have hnY (y : Space) : 0 ≤ Y y := (norm_nonneg _).trans (hYh y)
  have hnZ (y : Space) : 0 ≤ Z y := (norm_nonneg _).trans (hZh y)
  filter_upwards [hd.first,hd.second,hd.fourth,hd.fifth,hd.sixth] with x h1 h2 h4 h5 h6
  have hb := (cross_pair_pointwise ha hc hu hU hh hH hAu hBu hYh hZh hAv hBv hYk hZk x h1 h2 h4 h5 h6).trans
    (weightedMajorantSum_le ha hc hnA hnB hnY hnZ x)
  exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans hb,
    (le_add_of_nonneg_left (norm_nonneg _)).trans hb⟩

#print axioms cross_pair_pointwise
#print axioms cross_pair_ae
end HartreeF.CrossContinuity
