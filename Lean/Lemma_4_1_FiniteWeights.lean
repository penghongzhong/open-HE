import Lemma_4_1_AnisotropicScaling

/-! Exact finite nonnegative combinations of exterior-disk weights. This
proves the finite Stieltjes stage; general monotone weights and H1 density
are not asserted here. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace BWork.Kelvin

def finiteWeight {n : ℕ} (c₀ : ℝ) (c R : Fin n → ℝ) (z : Space) : ℝ :=
  c₀ + ∑ i, c i * (exteriorCylinder (R i)).indicator (fun _ => (1 : ℝ)) z

theorem finiteWeight_mul {n : ℕ} (c₀ : ℝ) (c R : Fin n → ℝ) (F : Space → ℝ) :
    (fun z => finiteWeight c₀ c R z * F z) =
      (fun z => c₀ * F z + ∑ i, c i * (exteriorCylinder (R i)).indicator F z) := by
  funext z
  simp only [finiteWeight,add_mul,Finset.sum_mul,mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  by_cases hz : z ∈ exteriorCylinder (R i) <;> simp [hz]

theorem finiteWeight_integrable {n : ℕ} (c₀ : ℝ) (c R : Fin n → ℝ)
    {F : Space → ℝ} (hF : Integrable F) :
    Integrable (fun z => finiteWeight c₀ c R z * F z) := by
  rw [finiteWeight_mul]
  apply (hF.const_mul c₀).add
  exact integrable_finsetSum _ (fun i _ =>
    (hF.indicator (MeasurableSet.univ.prod (exteriorDisk_measurable (R i)))).const_mul (c i))

theorem finiteWeight_integral {n : ℕ} (c₀ : ℝ) (c R : Fin n → ℝ)
    {F : Space → ℝ} (hF : Integrable F) :
    (∫ z, finiteWeight c₀ c R z * F z) =
      c₀ * (∫ z, F z) + ∑ i, c i * ∫ z in exteriorCylinder (R i), F z := by
  rw [finiteWeight_mul]
  have hi : ∀ i : Fin n, Integrable (fun z => c i * (exteriorCylinder (R i)).indicator F z) :=
    fun i => (hF.indicator (MeasurableSet.univ.prod (exteriorDisk_measurable (R i)))).const_mul (c i)
  rw [integral_add (hF.const_mul c₀) (integrable_finsetSum _ (fun i _ => hi i)),
    integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul]
  congr 1
  exact integral_indicator (MeasurableSet.univ.prod (exteriorDisk_measurable (R i)))

/-- Pure linear averaging, independent of Sobolev or Kelvin facts. -/
theorem finiteWeight_comparison {n : ℕ} {c₀ C : ℝ} (c R : Fin n → ℝ)
    (h₀ : 0 ≤ c₀) (hc : ∀ i, 0 ≤ c i) {F H : Space → ℝ}
    (hF : Integrable F) (hH : Integrable H)
    (hall : (∫ z, F z) ≤ C * ∫ z, H z)
    (htail : ∀ i, (∫ z in exteriorCylinder (R i), F z) ≤
      C * ∫ z in exteriorCylinder (R i), H z) :
    (∫ z, finiteWeight c₀ c R z * F z) ≤ C * ∫ z, finiteWeight c₀ c R z * H z := by
  rw [finiteWeight_integral _ _ _ hF,finiteWeight_integral _ _ _ hH,mul_add,
    Finset.mul_sum]
  apply add_le_add
  · nlinarith [mul_le_mul_of_nonneg_left hall h₀]
  · apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_le_mul_of_nonneg_left (htail i) (hc i)]

/-- The weighted paper estimate for every actual finite radial step weight. -/
theorem finiteWeight_anisotropic {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback) (glue : SmoothInterfaceGluing)
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {n : ℕ} {c₀ : ℝ} (c R : Fin n → ℝ) (h₀ : 0 ≤ c₀)
    (hc : ∀ i, 0 ≤ c i) (hR : ∀ i, 0 < R i) :
    (∫ z, finiteWeight c₀ c R z * f z^6) ≤
      (54/G^2 * (∫ z, transverseDensity (fderiv ℝ f) z)^2) *
        ∫ z, finiteWeight c₀ c R z * longitudinalDensity (fderiv ℝ f) z := by
  have hH : InH1 f (fderiv ℝ f) := by
    have h := glue (fun _ => (1 : ℝ)) f f contDiff_const
      (fun z hz => by norm_num at hz) (hf.of_le (by norm_num)) (hf.of_le (by norm_num))
      (fun _ _ => rfl)
    simpa only [not_lt_of_ge zero_le_one,ite_false] using h (by simpa using hcompact)
  apply finiteWeight_comparison c R h₀ hc (sharp f _ hH).1
    (longitudinalDensity_integrable hH.2.1)
  · have hi := anisotropic_sobolev hG sharp pullback hH
    have hB : 0 ≤ ∫ z, longitudinalDensity (fderiv ℝ f) z := integral_nonneg (fun z => sq_nonneg _)
    have hcoef : 27/(4*G^2) ≤ 54/G^2 := by
      have hG2 : 0 < G^2 := sq_pos_of_pos hG
      apply (div_le_div_iff₀ (by positivity : 0 < 4*G^2) hG2).mpr
      nlinarith
    exact hi.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)) hB)
  · intro i
    exact exterior_anisotropic hG (hR i) sharp pullback glue hf hcompact

#print axioms finiteWeight_mul
#print axioms finiteWeight_integrable
#print axioms finiteWeight_integral
#print axioms finiteWeight_comparison
#print axioms finiteWeight_anisotropic
end BWork.Kelvin
