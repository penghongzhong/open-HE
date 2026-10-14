import Lemma_4_1_ReparametrizedEnergy

/-! The symmetric finite-domain 9/4 energy bound, using actual product measures. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace BWork.Kelvin

abbrev PairSpace := ℝ × (Plane × Plane)

def pairMeasure (ν : Measure Plane) : Measure PairSpace := volume.prod (ν.prod ν)

def pairSwap : PairSpace ≃ᵐ PairSpace :=
  (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.prodComm : Plane × Plane ≃ᵐ Plane × Plane)

theorem pairSwap_preserving (ν : Measure Plane) [SFinite ν] :
    MeasurePreserving pairSwap (pairMeasure ν) (pairMeasure ν) :=
  (MeasurePreserving.id volume).prod Measure.measurePreserving_swap

theorem pairSwap_integral (ν : Measure Plane) [SFinite ν] (F : PairSpace → ℝ) :
    (∫ p,F (pairSwap p) ∂pairMeasure ν) = ∫ p,F p ∂pairMeasure ν :=
  (pairSwap_preserving ν).integral_comp' F

def pairMass (k : Plane × Plane → ℝ) (g d : Space → ℝ) (p : PairSpace) : ℝ :=
  k p.2*g (p.1,p.2.2)^2*d (p.1,p.2.1)^2

def pairError (k : Plane × Plane → ℝ) (d : Space → ℝ) (p : PairSpace) : ℝ :=
  k p.2*d (p.1,p.2.1)^2

def pairRegularizedEnergy (k : Plane × Plane → ℝ) (g d : Space → ℝ) (ε : ℝ)
    (p : PairSpace) : ℝ :=
  k p.2*regularizedEnergy (g (p.1,p.2.2)) (d (p.1,p.2.2)) ε (g (p.1,p.2.1)) (d (p.1,p.2.1))

theorem regularizedEnergy_nonneg (h h' g gs : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ regularizedEnergy h h' ε g gs := by
  have hH : 0 < h^2+ε := by positivity
  have hroot : (Real.sqrt (h^2+ε))^2 = h^2+ε := Real.sq_sqrt hH.le
  have hr : Real.sqrt (h^2+ε) ≠ 0 := (Real.sqrt_pos.mpr hH).ne'
  have he : regularizedEnergy h h' ε g gs =
      (Real.sqrt (h^2+ε)*gs+(h*h'/(2*Real.sqrt (h^2+ε)))*g)^2 := by
    unfold regularizedEnergy
    conv_lhs => rw [← hroot]
    field_simp
    ring
  rw [he]; exact sq_nonneg _

theorem regularizedEnergy_le (h h' g gs : ℝ) {ε : ℝ} (hε : 0 < ε) :
    regularizedEnergy h h' ε g gs ≤ 3/2*(h^2*gs^2)+3/4*(g^2*h'^2)+ε*gs^2 := by
  have hH : 0 < h^2+ε := by positivity
  have hr : h^2/(h^2+ε) ≤ 1 := (div_le_one hH).mpr (by linarith)
  have hlast : (h^2*h'^2)/(4*(h^2+ε))*g^2 ≤ (1/4)*(g^2*h'^2) := by
    calc
      _ = (h^2/(h^2+ε))*(g^2*h'^2/4) := by field_simp
      _ ≤ 1*(g^2*h'^2/4) := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by ring
  have hcross : h*h'*g*gs ≤ (h^2*gs^2+g^2*h'^2)/2 := by
    nlinarith [sq_nonneg (h*gs-g*h')]
  unfold regularizedEnergy
  nlinarith

theorem pairRegularizedEnergy_le {k : Plane × Plane → ℝ} (hk : ∀ p,0 ≤ k p)
    (hsym : ∀ y a,k (y,a)=k (a,y)) (g d : Space → ℝ)
    {ε : ℝ} (hε : 0 < ε) (p : PairSpace) :
    pairRegularizedEnergy k g d ε p ≤
      3/2*pairMass k g d p+3/4*pairMass k g d (pairSwap p)+ε*pairError k d p := by
  have h := mul_le_mul_of_nonneg_left
    (regularizedEnergy_le (g (p.1,p.2.2)) (d (p.1,p.2.2))
      (g (p.1,p.2.1)) (d (p.1,p.2.1)) hε) (hk p.2)
  change k p.2*regularizedEnergy _ _ _ _ _ ≤ _
  change k p.2*regularizedEnergy _ _ _ _ _ ≤ _ at h
  unfold pairMass pairError
  change _ ≤ 3/2*(k p.2*g (p.1,p.2.2)^2*d (p.1,p.2.1)^2)+
    3/4*(k (p.2.2,p.2.1)*g (p.1,p.2.1)^2*d (p.1,p.2.2)^2)+ε*(k p.2*d (p.1,p.2.1)^2)
  rw [← hsym p.2.1 p.2.2]
  nlinarith

theorem pairRegularizedEnergy_measurable {k : Plane × Plane → ℝ}
    (hk : Measurable k) {g d : Space → ℝ} (hg : Measurable g) (hd : Measurable d) (ε : ℝ) :
    Measurable (pairRegularizedEnergy k g d ε) := by
  unfold pairRegularizedEnergy regularizedEnergy
  fun_prop

/-- Pointwise nonnegativity and the proved symmetric bound supply integrability;
no integrability of the transformed energy is postulated. -/
theorem pairRegularizedEnergy_integrable (ν : Measure Plane) [SFinite ν]
    {k : Plane × Plane → ℝ} (hkm : Measurable k) (hk : ∀ p,0 ≤ k p)
    (hsym : ∀ y a,k (y,a)=k (a,y)) {g d : Space → ℝ}
    (hg : Measurable g) (hd : Measurable d) {ε : ℝ} (hε : 0 < ε)
    (hI : Integrable (pairMass k g d) (pairMeasure ν))
    (hC : Integrable (pairError k d) (pairMeasure ν)) :
    Integrable (pairRegularizedEnergy k g d ε) (pairMeasure ν) := by
  have hs := (pairSwap_preserving ν).integrable_comp_of_integrable hI
  have hmajor := ((hI.const_mul (3/2)).add (hs.const_mul (3/4))).add (hC.const_mul ε)
  apply hmajor.mono' (pairRegularizedEnergy_measurable hkm hg hd ε).aestronglyMeasurable
  filter_upwards [] with p
  unfold pairRegularizedEnergy
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hk p.2)
    (regularizedEnergy_nonneg _ _ _ _ hε))]
  exact pairRegularizedEnergy_le hk hsym g d hε p

theorem pairRegularizedEnergy_integral_le (ν : Measure Plane) [SFinite ν]
    {k : Plane × Plane → ℝ} (hkm : Measurable k) (hk : ∀ p,0 ≤ k p)
    (hsym : ∀ y a,k (y,a)=k (a,y)) {g d : Space → ℝ}
    (hg : Measurable g) (hd : Measurable d) {ε : ℝ} (hε : 0 < ε)
    (hI : Integrable (pairMass k g d) (pairMeasure ν))
    (hC : Integrable (pairError k d) (pairMeasure ν)) :
    (∫ p,pairRegularizedEnergy k g d ε p ∂pairMeasure ν) ≤
      9/4*(∫ p,pairMass k g d p ∂pairMeasure ν)+ε*∫ p,pairError k d p ∂pairMeasure ν := by
  have hs := (pairSwap_preserving ν).integrable_comp_of_integrable hI
  have he := pairRegularizedEnergy_integrable ν hkm hk hsym hg hd hε hI hC
  have hm := integral_mono he
    (((hI.const_mul (3/2)).add (hs.const_mul (3/4))).add (hC.const_mul ε))
    (pairRegularizedEnergy_le hk hsym g d hε)
  dsimp only [Pi.add_apply] at hm
  have hsplit := integral_add ((hI.const_mul (3/2)).add (hs.const_mul (3/4))) (hC.const_mul ε)
  have hsplit₂ := integral_add (hI.const_mul (3/2)) (hs.const_mul (3/4))
  dsimp only [Pi.add_apply] at hsplit hsplit₂
  rw [hsplit,hsplit₂] at hm
  simp_rw [integral_const_mul] at hm
  dsimp only [Function.comp_def] at hm
  rw [pairSwap_integral ν] at hm
  linarith

theorem pairDerivative_integrable (ν : Measure Plane) [IsFiniteMeasure ν]
    {d : Space → ℝ} (hD : Integrable (fun z => d z^2) (volume.prod ν)) :
    Integrable (fun p : PairSpace => d (p.1,p.2.1)^2) (pairMeasure ν) := by
  have hp := hD.comp_fst ν
  exact ((measurePreserving_prodAssoc volume ν ν).integrable_comp_emb
    MeasurableEquiv.prodAssoc.measurableEmbedding).mp hp

theorem pairMoments_integrable (ν : Measure Plane) [IsFiniteMeasure ν]
    {k : Plane × Plane → ℝ} (hkm : Measurable k) (hk : ∀ p,0 ≤ k p)
    {K : ℝ} (hK : ∀ p,k p ≤ K) {g d : Space → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ z,g z^2 ≤ M)
    (hD : Integrable (fun z => d z^2) (volume.prod ν)) :
    Integrable (pairMass k g d) (pairMeasure ν) ∧
      Integrable (pairError k d) (pairMeasure ν) := by
  have hd := pairDerivative_integrable ν hD
  constructor
  · apply hd.bdd_mul (c := K*M)
    · have hm : Measurable (fun p : PairSpace => k p.2*g (p.1,p.2.2)^2) := by fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [] with p
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hk _) (sq_nonneg _))]
      exact mul_le_mul (hK _) (hM _) (sq_nonneg _) ((hk p.2).trans (hK p.2))
  · apply hd.bdd_mul (c := K) (hkm.comp measurable_snd).aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs,abs_of_nonneg (hk _)]
    exact hK _

/-- Genuine finite-measure 9/4 bound with all pair integrability derived from
a bounded amplitude, a bounded nonnegative symmetric kernel and L2 derivative. -/
theorem nine_quarters_finite (ν : Measure Plane) [IsFiniteMeasure ν]
    {k : Plane × Plane → ℝ} (hkm : Measurable k) (hk : ∀ p,0 ≤ k p)
    (hsym : ∀ y a,k (y,a)=k (a,y)) {K : ℝ} (hK : ∀ p,k p ≤ K)
    {g d : Space → ℝ} (hg : Measurable g) (hd : Measurable d)
    {M : ℝ} (hM : ∀ z,g z^2 ≤ M) {ε : ℝ} (hε : 0 < ε)
    (hD : Integrable (fun z => d z^2) (volume.prod ν)) :
    (∫ p,pairRegularizedEnergy k g d ε p ∂pairMeasure ν) ≤
      9/4*(∫ p,pairMass k g d p ∂pairMeasure ν)+ε*∫ p,pairError k d p ∂pairMeasure ν := by
  obtain ⟨hI,hC⟩ := pairMoments_integrable ν hkm hk hK hg hM hD
  exact pairRegularizedEnergy_integral_le ν hkm hk hsym hg hd hε hI hC

#print axioms pairSwap_preserving
#print axioms pairSwap_integral
#print axioms regularizedEnergy_nonneg
#print axioms regularizedEnergy_le
#print axioms pairRegularizedEnergy_le
#print axioms pairRegularizedEnergy_measurable
#print axioms pairRegularizedEnergy_integrable
#print axioms pairRegularizedEnergy_integral_le
#print axioms pairDerivative_integrable
#print axioms pairMoments_integrable
#print axioms nine_quarters_finite
end BWork.Kelvin
