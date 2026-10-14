import Lemma_4_1_FiniteWeights
import Mathlib.MeasureTheory.Measure.Stieltjes

/-! Native Stieltjes averaging for bounded monotone radial weights.
No additional analytic interface is introduced. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

def closedTail (t : ℝ) : Set Space := {z | t ≤ radiusSq z}

theorem closedTail_measurable (t : ℝ) : MeasurableSet (closedTail t) :=
  (isClosed_le continuous_const radiusSq_contDiff.continuous).measurableSet

theorem cylinder_level_zero (t : ℝ) : volume {z : Space | radiusSq z = t} = 0 := by
  apply Measure.measure_prod_null_of_ae_null
  · exact (isClosed_eq radiusSq_contDiff.continuous continuous_const).measurableSet
  · filter_upwards [] with x
    exact circle_measure_zero t

theorem ae_radiusSq_avoids {N : Set ℝ} (hN : N.Countable) :
    ∀ᵐ z : Space, radiusSq z ∉ N := by
  have h (t : N) : ∀ᵐ z : Space, radiusSq z ≠ (t : ℝ) := by
    simpa only [ae_iff,not_not] using cylinder_level_zero t
  have := hN.to_subtype
  filter_upwards [ae_all_iff.mpr h] with z hz
  intro hmem
  exact hz ⟨radiusSq z,hmem⟩ rfl

theorem closedTail_ae_exterior {t : ℝ} (ht : 0 < t) :
    closedTail t =ᵐ[volume] exteriorCylinder (Real.sqrt t) := by
  have hn : ∀ᵐ z : Space, radiusSq z ≠ t := by
    simpa only [ae_iff,not_not] using cylinder_level_zero t
  filter_upwards [hn] with z hz
  apply propext
  simp only [closedTail,mem_ofPred_eq,exteriorCylinder,mem_prod,mem_univ,true_and,
    exteriorDisk,Real.sq_sqrt ht.le]
  change (t ≤ radiusSq z) ↔ (t < radiusSq z)
  exact ⟨fun h => lt_of_le_of_ne h hz.symm,le_of_lt⟩

def stieltjesKernel (F : Space → ℝ) (p : ℝ × Space) : ℝ :=
  {q : ℝ × Space | q.1 ≤ radiusSq q.2}.indicator (fun q => F q.2) p

theorem stieltjesKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {F : Space → ℝ} (hF : Integrable F) :
    Integrable (stieltjesKernel F) (μ.prod volume) := by
  apply (hF.comp_snd μ).indicator
  exact (isClosed_le continuous_fst (radiusSq_contDiff.continuous.comp continuous_snd)).measurableSet

theorem stieltjesKernel_slice (F : Space → ℝ) (t : ℝ) (z : Space) :
    stieltjesKernel F (t,z) = (closedTail t).indicator F z := by
  by_cases h : t ≤ radiusSq z <;> simp [stieltjesKernel,closedTail,indicator,h]

def stieltjesWeight (c : ℝ) (μ : Measure ℝ) (z : Space) : ℝ :=
  c + ∫ t, (closedTail t).indicator (fun _ => (1 : ℝ)) z ∂μ

theorem stieltjesWeight_integrable (c : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {F : Space → ℝ} (hF : Integrable F) :
    Integrable (fun z => stieltjesWeight c μ z * F z) := by
  have he (z : Space) : stieltjesWeight c μ z * F z =
      c*F z + ∫ t, stieltjesKernel F (t,z) ∂μ := by
    rw [stieltjesWeight,add_mul,← integral_mul_const]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases hz : z ∈ closedTail t <;> simp [stieltjesKernel_slice,hz]
  simp_rw [he]
  exact (hF.const_mul c).add ((stieltjesKernel_integrable μ hF).integral_prod_right)

theorem stieltjesWeight_integral (c : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {F : Space → ℝ} (hF : Integrable F) :
    (∫ z, stieltjesWeight c μ z * F z) =
      c*(∫ z,F z) + ∫ t, (∫ z in closedTail t,F z) ∂μ := by
  have he (z : Space) : stieltjesWeight c μ z * F z =
      c*F z + ∫ t, stieltjesKernel F (t,z) ∂μ := by
    rw [stieltjesWeight,add_mul,← integral_mul_const]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases hz : z ∈ closedTail t <;> simp [stieltjesKernel_slice,hz]
  simp_rw [he]
  rw [integral_add (hF.const_mul c) ((stieltjesKernel_integrable μ hF).integral_prod_right),
    integral_const_mul]
  rw [integral_integral_swap (f := fun z t => stieltjesKernel F (t,z))
    (stieltjesKernel_integrable μ hF).swap]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp_rw [stieltjesKernel_slice]
  exact integral_indicator (closedTail_measurable t)

theorem stieltjesWeight_comparison {c C : ℝ} (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hc : 0 ≤ c) {F H : Space → ℝ} (hF : Integrable F) (hH : Integrable H)
    (hall : (∫ z,F z) ≤ C*∫ z,H z)
    (htail : ∀ᵐ t ∂μ, (∫ z in closedTail t,F z) ≤ C*∫ z in closedTail t,H z) :
    (∫ z,stieltjesWeight c μ z*F z) ≤ C*∫ z,stieltjesWeight c μ z*H z := by
  rw [stieltjesWeight_integral c μ hF,stieltjesWeight_integral c μ hH,mul_add]
  apply add_le_add
  · nlinarith [mul_le_mul_of_nonneg_left hall hc]
  · have hFi := (stieltjesKernel_integrable μ hF).integral_prod_left
    have hHi := (stieltjesKernel_integrable μ hH).integral_prod_left
    have he (K : Space → ℝ) (t : ℝ) :
        (∫ z,stieltjesKernel K (t,z)) = ∫ z in closedTail t,K z := by
      simp_rw [stieltjesKernel_slice]
      exact integral_indicator (closedTail_measurable t)
    simp_rw [he] at hFi hHi
    simpa only [integral_const_mul] using integral_mono_ae hFi (hHi.const_mul C) htail

/-- The Stieltjes measure of a right-continuous monotone function represents
its increment from zero, including every jump with the correct endpoint. -/
theorem stieltjesWeight_eq (f : StieltjesFunction ℝ)
    [IsFiniteMeasure f.measure] (z : Space) :
    stieltjesWeight (f 0) (f.measure.restrict (Ioi 0)) z = f (radiusSq z) := by
  have he : (fun t => (closedTail t).indicator (fun _ => (1 : ℝ)) z) =
      (Iic (radiusSq z)).indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases h : t ≤ radiusSq z <;> simp [closedTail,indicator,h]
  rw [stieltjesWeight,he,integral_indicator measurableSet_Iic,setIntegral_const]
  simp only [smul_eq_mul,mul_one]
  change f 0 + (f.measure.restrict (Ioi 0) (Iic (radiusSq z))).toReal = _
  rw [Measure.restrict_apply measurableSet_Iic]
  have hi : Iic (radiusSq z) ∩ Ioi (0 : ℝ) = Ioc 0 (radiusSq z) := by
    ext t; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc,and_comm]
  rw [hi,f.measure_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono (radiusSq_nonneg z)))]
  ring

/-- Every bounded nonnegative monotone weight has an actual finite Stieltjes
representation almost everywhere after composition with the squared radius.
Countably many jump cylinders are explicitly discarded as null sets. -/
theorem monotone_stieltjes_representation {b : ℝ → ℝ} (hb : Monotone b)
    (h₀ : ∀ t,0 ≤ b t) (hbound : ∃ M,∀ t,b t ≤ M) :
    ∃ (c : ℝ) (μ : Measure ℝ), 0 ≤ c ∧ IsFiniteMeasure μ ∧
      (∀ᵐ t ∂μ,0 < t) ∧ (fun z : Space => b (radiusSq z)) =ᵐ[volume] stieltjesWeight c μ := by
  obtain ⟨M,hM⟩ := hbound
  let f := hb.stieltjesFunction
  have hf₀ (t : ℝ) : 0 ≤ f t := (h₀ t).trans (hb.le_rightLim le_rfl)
  have hfM (t : ℝ) : f t ≤ M := (hb.rightLim_le (lt_add_one t)).trans (hM (t+1))
  have hfin : IsFiniteMeasure f.measure :=
    f.isFiniteMeasure_of_forall_abs_le (fun t => by rw [abs_of_nonneg (hf₀ t)]; exact hfM t)
  refine ⟨f 0,f.measure.restrict (Ioi 0),hf₀ 0,inferInstance,?_,?_⟩
  · exact ae_restrict_mem measurableSet_Ioi
  · filter_upwards [ae_radiusSq_avoids hb.countable_not_continuousAt] with z hz
    rw [stieltjesWeight_eq]
    have hcont : ContinuousAt b (radiusSq z) := not_not.mp hz
    exact hcont.continuousWithinAt.rightLim_eq.symm

/-- Tail comparisons imply comparison against every bounded monotone radial
weight. This is proved by native Bochner Fubini and the native Stieltjes measure. -/
theorem monotoneWeight_comparison {b : ℝ → ℝ} (hb : Monotone b)
    (h₀ : ∀ t,0 ≤ b t) (hbound : ∃ M,∀ t,b t ≤ M)
    {F H : Space → ℝ} {C : ℝ} (hF : Integrable F) (hH : Integrable H)
    (hall : (∫ z,F z) ≤ C*∫ z,H z)
    (htail : ∀ t,0 < t → (∫ z in closedTail t,F z) ≤ C*∫ z in closedTail t,H z) :
    (∫ z,b (radiusSq z)*F z) ≤ C*∫ z,b (radiusSq z)*H z := by
  obtain ⟨c,μ,hc,hfin,hpos,he⟩ := monotone_stieltjes_representation hb h₀ hbound
  have hFe : (fun z => b (radiusSq z)*F z) =ᵐ[volume]
      (fun z => stieltjesWeight c μ z*F z) := he.mul (Filter.EventuallyEq.rfl)
  have hHe : (fun z => b (radiusSq z)*H z) =ᵐ[volume]
      (fun z => stieltjesWeight c μ z*H z) := he.mul (Filter.EventuallyEq.rfl)
  rw [integral_congr_ae hFe,integral_congr_ae hHe]
  exact stieltjesWeight_comparison μ hc hF hH hall (hpos.mono fun t ht => htail t ht)

def radialWeight (b : ℝ → ℝ) (z : Space) : ℝ := b (Real.sqrt (radiusSq z))

/-- Equation (14) for every bounded nonnegative nondecreasing radial weight
and every real smooth compactly supported function. No continuity of b is assumed. -/
theorem radialWeight_anisotropic_smooth {G : ℝ} (hG : 0 < G)
    (sharp : SharpSobolev G) (pullback : LinearSobolevPullback) (glue : SmoothInterfaceGluing)
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {b : ℝ → ℝ} (hb : MonotoneOn b (Ici 0)) (h₀ : ∀ r,0 ≤ r → 0 ≤ b r)
    (hbound : ∃ M,∀ r,0 ≤ r → b r ≤ M) :
    (∫ z,radialWeight b z*f z^6) ≤
      (54/G^2*(∫ z,transverseDensity (fderiv ℝ f) z)^2)*
        ∫ z,radialWeight b z*longitudinalDensity (fderiv ℝ f) z := by
  have hH : InH1 f (fderiv ℝ f) := by
    have h := glue (fun _ => (1 : ℝ)) f f contDiff_const
      (fun z hz => by norm_num at hz) (hf.of_le (by norm_num)) (hf.of_le (by norm_num))
      (fun _ _ => rfl)
    simpa only [not_lt_of_ge zero_le_one,ite_false] using h (by simpa using hcompact)
  have hmono : Monotone (fun t => b (Real.sqrt t)) :=
    fun _ _ h => hb (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt h)
  apply monotoneWeight_comparison hmono (fun t => h₀ _ (Real.sqrt_nonneg t))
    (by obtain ⟨M,hM⟩ := hbound; exact ⟨M,fun t => hM _ (Real.sqrt_nonneg t)⟩)
    (sharp f _ hH).1 (longitudinalDensity_integrable hH.2.1)
  · have h := finiteWeight_anisotropic hG sharp pullback glue hf hcompact
      (n := 0) (c₀ := 1) (fun _ => 0) (fun _ => 1) zero_le_one
      (fun _ => le_refl 0) (fun _ => zero_lt_one)
    simpa only [finiteWeight,Fin.sum_univ_zero,add_zero,one_mul] using h
  · intro t ht
    rw [setIntegral_congr_set (closedTail_ae_exterior ht),
      setIntegral_congr_set (closedTail_ae_exterior ht)]
    exact exterior_anisotropic hG (Real.sqrt_pos.mpr ht) sharp pullback glue hf hcompact

#print axioms closedTail_measurable
#print axioms cylinder_level_zero
#print axioms ae_radiusSq_avoids
#print axioms closedTail_ae_exterior
#print axioms stieltjesKernel_integrable
#print axioms stieltjesKernel_slice
#print axioms stieltjesWeight_integrable
#print axioms stieltjesWeight_integral
#print axioms stieltjesWeight_comparison
#print axioms stieltjesWeight_eq
#print axioms monotone_stieltjes_representation
#print axioms monotoneWeight_comparison
#print axioms radialWeight_anisotropic_smooth
end BWork.Kelvin
