import FCompactCrossTerms
import DirectionalCriticalDifference

/-! Independent source and recipient labels. All estimates are on the literal
Riesz integrals and on the sum of the norms of the two placements. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.CrossContinuity
open ForcingDomain WeakHartreeChain DerivativeMajorization GradientMajorants

def innerField (α c : ℝ) (u h v : Space → ℂ) : Space → ℂ :=
  fun x => rieszConvolution α c (directionalDensity α u h) x •
    WeakHartreeChain.localFactor (1+α) (v x)

def outerField (α c : ℝ) (u v k : Space → ℂ) : Space → ℂ :=
  fun x => potential α c u x • localFactorDerivative (1+α) (v x) (k x)

theorem generalized_potential_envelopes {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {u U : Space → ℂ} {A B : Space → ℝ}
    (hu : AEStronglyMeasurable u volume) (hU : AEStronglyMeasurable U volume)
    (hA : ∀ y, sumAmplitude u U y ≤ A y)
    (hB : ∀ y, differenceAmplitude u U y ≤ B y) (x : Space)
    (hbase : Integrable (fun y => rieszKernel α c (x-y)*A y^(3+α)) volume)
    (hdiff : Integrable (fun y => rieszKernel α c (x-y)*(A y^(2+α)*B y)) volume) :
    ‖potential α c u x‖ ≤ rieszConvolution α c (fun y => A y^(3+α)) x ∧
    ‖potential α c u x-potential α c U x‖ ≤
      (3+α)*rieszConvolution α c (fun y => A y^(2+α)*B y) x := by
  have hn (y : Space) : 0 ≤ A y := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hA y)
  have hm (f : Space → ℂ) (hf : AEStronglyMeasurable f volume) :
      AEStronglyMeasurable (powerDensity α f) volume :=
    (density_contDiff_one (by linarith : 1<3+α)).continuous.comp_aestronglyMeasurable hf
  have hb (f : Space → ℂ) (hf : ∀ y, ‖f y‖ ≤ A y) (y : Space) :
      ‖powerDensity α f y‖ ≤ A y^(3+α) := by
    rw [powerDensity, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_le_rpow (norm_nonneg _) (hf y) (by linarith)
  have huA (y : Space) : ‖u y‖ ≤ A y :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hA y)
  have hUA (y : Space) : ‖U y‖ ≤ A y :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hA y)
  obtain ⟨hui,hun⟩ := riesz_fibre_norm_domination hc x (hm u hu) hbase (hb u huA)
  obtain ⟨hUi,_⟩ := riesz_fibre_norm_domination hc x (hm U hU) hbase (hb U hUA)
  refine ⟨hun, riesz_difference_norm_const_domination hc x (hm u hu) (hm U hU) hui hUi hdiff ?_⟩
  intro y
  have ht := density_difference_bound (by linarith : 1<3+α) (u y) (U y)
  simp only [WeakHartreeChain.density, show 3+α-1=2+α by ring] at ht
  change ‖powerDensity α u y-powerDensity α U y‖ ≤ _ at ht
  apply ht.trans
  dsimp [sumAmplitude,differenceAmplitude] at hA hB
  have hAn := hn y
  calc
    _ ≤ (3+α)*A y^(2+α)*B y := by
      gcongr
      · exact hA y
      · exact hB y
    _ = _ := by ring

theorem generalized_density_envelopes {α c : ℝ} (ha : 0<α) (hc : 0≤c)
    {u U h H : Space → ℂ} {A B Y Z : Space → ℝ}
    (hu : AEStronglyMeasurable u volume) (hU : AEStronglyMeasurable U volume)
    (hh : AEStronglyMeasurable h volume) (hH : AEStronglyMeasurable H volume)
    (hA : ∀ y, sumAmplitude u U y ≤ A y)
    (hB : ∀ y, differenceAmplitude u U y ≤ B y)
    (hY : ∀ y, ‖H y‖ ≤ Y y) (hZ : ∀ y, ‖h y-H y‖ ≤ Z y) (x : Space)
    (hdZ : Integrable (fun y => rieszKernel α c (x-y)*(A y^(2+α)*Z y)) volume)
    (hdBY : Integrable (fun y => rieszKernel α c (x-y)*(A y^(1+α)*B y*Y y)) volume)
    (hdY : Integrable (fun y => rieszKernel α c (x-y)*(A y^(2+α)*Y y)) volume) :
    ‖rieszConvolution α c (directionalDensity α U H) x‖ ≤
      (3+α)*rieszConvolution α c (fun y => A y^(2+α)*Y y) x ∧
    ‖rieszConvolution α c (directionalDensity α u h) x-
      rieszConvolution α c (directionalDensity α U H) x‖ ≤
      (3+α)*rieszConvolution α c (fun y => A y^(2+α)*Z y) x+
      ((3+α)*(2+α))*rieszConvolution α c (fun y => A y^(1+α)*B y*Y y) x := by
  have hnA (y : Space) : 0 ≤ A y := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hA y)
  have hnB (y : Space) : 0 ≤ B y := (norm_nonneg _).trans (hB y)
  have hnY (y : Space) : 0 ≤ Y y := (norm_nonneg _).trans (hY y)
  have hmU := directionalDensity_measurable α hu hh
  have hmV := directionalDensity_measurable α hU hH
  have hboundV (y : Space) : ‖directionalDensity α U H y‖ ≤ (3+α)*(A y^(2+α)*Y y) := by
    have ht := densityDerivative_action_bound_right (by linarith : 1<3+α) (u y) (U y) (H y)
    simp only [show 3+α-1=2+α by ring] at ht
    change ‖directionalDensity α U H y‖ ≤ _ at ht
    apply ht.trans
    dsimp [sumAmplitude] at hA
    have hAn := hnA y
    calc
      _ ≤ (3+α)*A y^(2+α)*Y y := by
        gcongr
        · exact hA y
        · exact hY y
      _ = _ := by ring
  obtain ⟨hVi,hVn⟩ := riesz_fibre_norm_const_domination hc x hmV hdY hboundV
  have hboundD (y : Space) : ‖directionalDensity α u h y-directionalDensity α U H y‖ ≤
      (3+α)*(A y^(2+α)*Z y)+((3+α)*(2+α))*(A y^(1+α)*B y*Y y) := by
    have ht := densityDerivative_action_difference (by linarith : 3<3+α) (u y) (U y) (h y) (H y)
    simp only [show 3+α-1=2+α by ring, show 3+α-2=1+α by ring] at ht
    change ‖directionalDensity α u h y-directionalDensity α U H y‖ ≤ _ at ht
    apply ht.trans
    dsimp [sumAmplitude,differenceAmplitude] at hA hB
    have hAn := hnA y
    have hBn := hnB y
    calc
      _ ≤ (3+α)*A y^(2+α)*Z y+(3+α)*(2+α)*A y^(1+α)*B y*Y y := by
        gcongr <;> first | exact hA y | exact hB y | exact hY y | exact hZ y
      _ = _ := by ring
  obtain ⟨hDi,hDn⟩ := riesz_two_envelope_domain hc x (hmU.sub hmV) hdZ hdBY hboundD
  have hUi : Integrable (fun y => rieszKernel α c (x-y)*directionalDensity α u h y) volume := by
    apply (hDi.add hVi).congr
    filter_upwards [] with y
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  rw [riesz_subtraction_of_domains x hUi hVi] at hDn
  exact ⟨hVn,hDn⟩

#print axioms generalized_potential_envelopes
#print axioms generalized_density_envelopes
end HartreeF.CrossContinuity
