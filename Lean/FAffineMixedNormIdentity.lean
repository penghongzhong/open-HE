import FAffineMeasurePushforward

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace HartreeF.AffineMixed
open CriticalAffine TimeHolder

/-- Reciprocal exponent, zero at infinity; this is not a replacement of essSup. -/
def reciprocalExponent (p : ℝ≥0∞) : ℝ := (1/p).toReal

/-- Positive finite scalar multiplication of an extended norm, including the
actual p=infinity essential-supremum branch of eLpNorm. -/
theorem eLpNorm_ennreal_const_mul {T : Type*} [MeasurableSpace T] (μ : Measure T)
    (p : ℝ≥0∞) {g : T → ℝ≥0∞} (hg : AEStronglyMeasurable g μ)
    {d : ℝ≥0∞} (hd0 : d≠0) (hdt : d≠∞) :
    eLpNorm (fun t => d*g t) p μ=d*eLpNorm g p μ := by
  have hm : AEStronglyMeasurable (fun t => d*g t) μ :=
    (hg.aemeasurable.const_mul d).aestronglyMeasurable
  apply le_antisymm
  · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p hm
      (ae_of_all _ (fun _ => by simp only [enorm_eq_self]; exact le_rfl))
  · have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p hg (c := d⁻¹)
      (g := fun t => d*g t) (ae_of_all _ (fun _ => by
        simp only [enorm_eq_self,← mul_assoc,ENNReal.inv_mul_cancel hd0 hdt,one_mul]; exact le_rfl))
    calc
      _ ≤ d*(d⁻¹*eLpNorm (fun t => d*g t) p μ) := mul_le_mul_right h d
      _ = _ := by rw [← mul_assoc,ENNReal.mul_inv_cancel hd0 hdt,one_mul]

theorem jacobian_rpow {a : ℝ} (ha : 0<a) (d : ℕ) (r : ℝ) :
    ENNReal.ofReal ((a^d)⁻¹)^r=ENNReal.ofReal (a^(-(d:ℝ)*r)) := by
  rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (pow_pos ha d))]
  have he : (a^d)⁻¹=a^(-(d:ℝ)) := by rw [Real.rpow_neg ha.le]; simp
  rw [he,← Real.rpow_mul ha.le]

/-- Exact extended spatial norm scaling for the literal representative. -/
theorem spatial_eLpNorm_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} (ha : 0<a) (b : Space) (k : ℝ) (q : ℝ≥0∞) (f : Space → E) :
    eLpNorm (fun x => a^k • f (affine a b x)) q volume=
      ENNReal.ofReal (a^(k-3*reciprocalExponent q))*eLpNorm f q volume := by
  have hm : eLpNorm f q (Measure.map (affine a b) volume)=eLpNorm (f ∘ affine a b) q volume :=
    (affineHomeomorph ha.ne' b).toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
  rw [affine_map_volume ha b,eLpNorm_smul_measure_of_ne_zero (by positivity)] at hm
  change eLpNorm ((a^k) • (f ∘ affine a b)) q volume=_
  rw [eLpNorm_const_smul,Real.enorm_of_nonneg (Real.rpow_nonneg ha.le k),← hm]
  simp only [smul_eq_mul]
  rw [← mul_assoc,jacobian_rpow ha 3,← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le k),
    ← Real.rpow_add ha]
  congr 2
  unfold reciprocalExponent
  norm_num
  ring

/-- Exact restricted-time norm scaling, valid also for time exponent infinity. -/
theorem time_eLpNorm_affine {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {a : ℝ} (ha : 0<a) (c : ℝ) (S : Set ℝ) (p : ℝ≥0∞) (g : ℝ → E) :
    eLpNorm (g ∘ timeAffine a c) p (volume.restrict ((timeAffine a c) ⁻¹' S))=
      ENNReal.ofReal (a^(-2*reciprocalExponent p))*eLpNorm g p (volume.restrict S) := by
  have hm : eLpNorm g p (Measure.map (timeAffine a c)
      (volume.restrict ((timeAffine a c) ⁻¹' S)))=
      eLpNorm (g ∘ timeAffine a c) p (volume.restrict ((timeAffine a c) ⁻¹' S)) :=
    (timeAffineHomeomorph ha c).toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
  rw [timeAffine_map_restrict ha c S,eLpNorm_smul_measure_of_ne_zero (by positivity)] at hm
  simpa only [smul_eq_mul,jacobian_rpow ha 2,reciprocalExponent,Nat.cast_ofNat] using hm.symm

def parabolicField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (b : Space) (c k : ℝ) (f : ℝ → Space → E) : ℝ → Space → E :=
  fun t x => a^k • f (timeAffine a c t) (affine a b x)

/-- Literal restricted-time mixed-norm covariance. No finite global norm is
assumed, and the original source time set S is transported by its exact preimage. -/
theorem mixedNorm_parabolicField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {a : ℝ} (ha : 0<a) (b : Space) (c k : ℝ) (S : Set ℝ)
    (p q : ℝ≥0∞) (hq0 : q≠0) (hqt : q≠∞) (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) ((volume.restrict S).prod volume)) :
    mixedNorm (volume.restrict ((timeAffine a c) ⁻¹' S)) volume p q (parabolicField a b c k f)=
      ENNReal.ofReal (a^(k-3*reciprocalExponent q-2*reciprocalExponent p))*
        mixedNorm (volume.restrict S) volume p q f := by
  have hg := spatial_lp_time_measurable (volume.restrict S) volume q hq0 hqt f hf
  have ht : AEStronglyMeasurable ((fun t => eLpNorm (f t) q volume) ∘ timeAffine a c)
      (volume.restrict ((timeAffine a c) ⁻¹' S)) := by
    apply (timeAffineHomeomorph ha c).toMeasurableEquiv.measurableEmbedding.aestronglyMeasurable_map_iff.mp
    change AEStronglyMeasurable (fun t => eLpNorm (f t) q volume)
      (Measure.map (timeAffine a c) (volume.restrict ((timeAffine a c) ⁻¹' S)))
    rw [timeAffine_map_restrict ha c S]
    exact hg.smul_measure _
  unfold mixedNorm parabolicField
  simp_rw [spatial_eLpNorm_affine ha b k q]
  have hmul := eLpNorm_ennreal_const_mul _ p ht
    (d := ENNReal.ofReal (a^(k-3*reciprocalExponent q))) (by positivity) ENNReal.ofReal_ne_top
  have htime := time_eLpNorm_affine ha c S p (fun t => eLpNorm (f t) q volume)
  simp only [Function.comp_apply] at hmul htime
  rw [hmul,htime,← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),← Real.rpow_add ha]
  congr 2
  ring

#print axioms reciprocalExponent
#print axioms eLpNorm_ennreal_const_mul
#print axioms jacobian_rpow
#print axioms spatial_eLpNorm_affine
#print axioms time_eLpNorm_affine
#print axioms parabolicField
#print axioms mixedNorm_parabolicField
end HartreeF.AffineMixed
