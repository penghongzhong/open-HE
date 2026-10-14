import FOrdinaryHomogeneousStrichartz
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-! Finite-cylinder domains for the actual jointly measurable Fourier free orbit.
This source is a static, uncompiled draft. No spacetime compactness is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
namespace HartreeF.FreeLocalCompactness
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
open FreeFlow ActualStrichartz

def cylinderMeasure (T R : ℝ) (z : V) : Measure (ℝ × V) :=
  (volume.restrict (Set.Icc (-T) T)).prod (volume.restrict (Metric.ball z R))

instance cylinderMeasure_finite (T R : ℝ) (z : V) :
    IsFiniteMeasure (cylinderMeasure T R z) := by
  have : IsFiniteMeasure ((volume : Measure V).restrict (Metric.ball z R)) :=
    isFiniteMeasure_restrict.mpr (Metric.isBounded_ball.measure_lt_top.ne)
  unfold cylinderMeasure
  infer_instance

theorem freeJoint_slice_memLp (f : L2) (t : ℝ) : MemLp (freeJoint f t) 2 volume :=
  (memLp_congr_ae (freeJoint_slice f t)).mpr (Lp.memLp (freeL2 t f))

theorem freeJoint_cylinder_slice_memLp (f : L2) (R : ℝ) (z : V) (t : ℝ) :
    MemLp (freeJoint f t) 2 (volume.restrict (Metric.ball z R)) :=
  (freeJoint_slice_memLp f t).restrict _

theorem freeJoint_slice_integral (f : L2) (t : ℝ) :
    (∫ x : V, ‖freeJoint f t x‖ ^ 2) = ‖f‖ ^ 2 := by
  calc
    _ = ∫ x : V, ‖freeL2 t f x‖ ^ 2 :=
      integral_congr_ae ((freeJoint_slice f t).fun_comp (fun a : ℂ => ‖a‖ ^ 2))
    _ = ‖freeL2 t f‖ ^ 2 := (l2_norm_sq_integral _).symm
    _ = ‖f‖ ^ 2 := by rw [freeL2_norm]

/-- This full-space, finite-time domain is obtained before any real norm is used. -/
theorem freeJoint_window_integrable_sq (f : L2) (T : ℝ) :
    Integrable (fun p : ℝ × V => ‖freeJoint f p.1 p.2‖ ^ 2)
      ((volume.restrict (Set.Icc (-T) T)).prod volume) := by
  apply (integrable_prod_iff
    ((freeJoint_stronglyMeasurable f).norm.pow 2).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun t => (freeJoint_slice_memLp f t).norm.integrable_sq)
  · have he : (fun t : ℝ => ∫ x : V, ‖‖freeJoint f t x‖ ^ 2‖) =
        (fun _ : ℝ => ‖f‖ ^ 2) := by
      funext t
      simp only [Real.norm_eq_abs, abs_pow, abs_norm]
      exact freeJoint_slice_integral f t
    simp only [Pi.pow_apply]
    rw [he]
    exact integrable_const _

theorem cylinderMeasure_le_window (T R : ℝ) (z : V) :
    cylinderMeasure T R z ≤ (volume.restrict (Set.Icc (-T) T)).prod volume :=
  Measure.prod_mono le_rfl Measure.restrict_le_self

theorem freeJoint_cylinder_integrable_sq (f : L2) (T R : ℝ) (z : V) :
    Integrable (fun p : ℝ × V => ‖freeJoint f p.1 p.2‖ ^ 2)
      (cylinderMeasure T R z) :=
  (freeJoint_window_integrable_sq f T).mono_measure (cylinderMeasure_le_window T R z)

theorem freeJoint_cylinder_memLp (f : L2) (T R : ℝ) (z : V) :
    MemLp (Function.uncurry (freeJoint f)) 2 (cylinderMeasure T R z) :=
  (memLp_two_iff_integrable_sq_norm
    (freeJoint_stronglyMeasurable f).aestronglyMeasurable).mpr
      (freeJoint_cylinder_integrable_sq f T R z)

theorem freeJoint_cylinder_integral_le (f : L2) {T R : ℝ} (hT : 0 ≤ T) (z : V) :
    (∫ p : ℝ × V, ‖freeJoint f p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z) ≤
      (2 * T) * ‖f‖ ^ 2 := by
  calc
    _ ≤ ∫ p : ℝ × V, ‖freeJoint f p.1 p.2‖ ^ 2
        ∂((volume.restrict (Set.Icc (-T) T)).prod volume) :=
      integral_mono_measure (cylinderMeasure_le_window T R z)
        (Eventually.of_forall (fun p => sq_nonneg _)) (freeJoint_window_integrable_sq f T)
    _ = ∫ t in Set.Icc (-T) T, ‖f‖ ^ 2 := by
      rw [integral_prod _ (freeJoint_window_integrable_sq f T)]
      simp only [freeJoint_slice_integral]
    _ = (2 * T) * ‖f‖ ^ 2 := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
        sub_neg_eq_add, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ T + T)]
      ring

/-- Equality of every-time spatial classes is promoted by measurable Fubini. -/
theorem joint_ae_of_slices {u v : ℝ → V → ℂ}
    (hu : StronglyMeasurable (Function.uncurry u))
    (hv : StronglyMeasurable (Function.uncurry v))
    (h : ∀ t, u t =ᵐ[volume] v t) (T R : ℝ) (z : V) :
    Function.uncurry u =ᵐ[cylinderMeasure T R z] Function.uncurry v := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hu.measurable hv.measurable)).mpr
  exact Eventually.of_forall (fun t => ae_restrict_of_ae (h t))

theorem freeJoint_cylinder_add_ae (f g : L2) (T R : ℝ) (z : V) :
    Function.uncurry (freeJoint (f + g)) =ᵐ[cylinderMeasure T R z]
      fun p => freeJoint f p.1 p.2 + freeJoint g p.1 p.2 := by
  refine joint_ae_of_slices (u := freeJoint (f + g))
    (v := fun t x => freeJoint f t x + freeJoint g t x)
    (by unfold Function.uncurry; exact freeJoint_stronglyMeasurable (f + g))
    (by unfold Function.uncurry
        change StronglyMeasurable ((fun z : ℝ × V => freeJoint f z.1 z.2) +
          (fun z : ℝ × V => freeJoint g z.1 z.2))
        exact (freeJoint_stronglyMeasurable f).add (freeJoint_stronglyMeasurable g)) ?_ T R z
  intro t
  filter_upwards [freeJoint_slice (f + g) t, freeJoint_slice f t, freeJoint_slice g t,
    Lp.coeFn_add (freeL2 t f) (freeL2 t g)] with x hfg hf hg hs
  rw [hfg, map_add, hs, Pi.add_apply, hf, hg]

theorem freeJoint_cylinder_sub_ae (f g : L2) (T R : ℝ) (z : V) :
    Function.uncurry (freeJoint (f - g)) =ᵐ[cylinderMeasure T R z]
      fun p => freeJoint f p.1 p.2 - freeJoint g p.1 p.2 := by
  refine joint_ae_of_slices (u := freeJoint (f - g))
    (v := fun t x => freeJoint f t x - freeJoint g t x)
    (by unfold Function.uncurry; exact freeJoint_stronglyMeasurable (f - g))
    (by unfold Function.uncurry
        change StronglyMeasurable ((fun z : ℝ × V => freeJoint f z.1 z.2) -
          (fun z : ℝ × V => freeJoint g z.1 z.2))
        exact (freeJoint_stronglyMeasurable f).sub (freeJoint_stronglyMeasurable g)) ?_ T R z
  intro t
  filter_upwards [freeJoint_slice (f - g) t, freeJoint_slice f t, freeJoint_slice g t,
    Lp.coeFn_sub (freeL2 t f) (freeL2 t g)] with x hfg hf hg hs
  rw [hfg, map_sub, hs, Pi.sub_apply, hf, hg]

theorem freeJoint_cylinder_smul_ae (a : ℂ) (f : L2) (T R : ℝ) (z : V) :
    Function.uncurry (freeJoint (a • f)) =ᵐ[cylinderMeasure T R z]
      fun p => a • freeJoint f p.1 p.2 := by
  refine joint_ae_of_slices (u := freeJoint (a • f))
    (v := fun t x => a • freeJoint f t x)
    (by unfold Function.uncurry; exact freeJoint_stronglyMeasurable (a • f))
    (by unfold Function.uncurry
        change StronglyMeasurable (a • (fun z : ℝ × V => freeJoint f z.1 z.2))
        exact (freeJoint_stronglyMeasurable f).const_smul a) ?_ T R z
  intro t
  filter_upwards [freeJoint_slice (a • f) t, freeJoint_slice f t,
    Lp.coeFn_smul a (freeL2 t f)] with x haf hf hs
  rw [haf, map_smul, hs, Pi.smul_apply, hf]

/-- Generic genuine-L2 conversion. The domain is a premise, never inferred from a total norm. -/
theorem eLpNorm_two_toReal_sq {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← Lp.norm_toLp f hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  exact integral_congr_ae (hf.coeFn_toLp.fun_comp (fun a : ℂ => ‖a‖ ^ 2))

theorem eLpNorm_two_eq_ofReal_sqrt {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {f : A → ℂ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  rw [← eLpNorm_two_toReal_sq hf, Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hf.eLpNorm_ne_top]

/-- Actual product/nested squared integral identity, with both domains supplied by Fubini. -/
theorem freeJoint_cylinder_integral_eq_nested (f : L2) (T R : ℝ) (z : V) :
    (∫ p : ℝ × V, ‖freeJoint f p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z) =
      ∫ t in Set.Icc (-T) T, ∫ x in Metric.ball z R, ‖freeJoint f t x‖ ^ 2 :=
  integral_prod _ (freeJoint_cylinder_integrable_sq f T R z)

theorem freeJoint_cylinder_norm_le (f : L2) {T R : ℝ} (hT : 0 ≤ T) (z : V) :
    (eLpNorm (Function.uncurry (freeJoint f)) 2 (cylinderMeasure T R z)).toReal ≤
      Real.sqrt (2 * T) * ‖f‖ := by
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (by positivity)).mp
  rw [eLpNorm_two_toReal_sq (freeJoint_cylinder_memLp f T R z), mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2 * T)]
  exact freeJoint_cylinder_integral_le f (R := R) hT z

/-- Equal exponents give the genuine nested/product L2 identity, including infinity. -/
theorem mixedNorm_two_eq_product {u : ℝ → V → ℂ}
    (hu : StronglyMeasurable (Function.uncurry u)) (T R : ℝ) (z : V) :
    TimeHolder.mixedNorm (volume.restrict (Set.Icc (-T) T))
      (volume.restrict (Metric.ball z R)) 2 2 u =
      eLpNorm (Function.uncurry u) 2 (cylinderMeasure T R z) := by
  have hs := TimeHolder.spatial_lp_time_measurable
    (volume.restrict (Set.Icc (-T) T)) (volume.restrict (Metric.ball z R))
    2 (by norm_num) (by norm_num) u hu.aestronglyMeasurable
  rw [TimeHolder.mixedNorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hs,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hu.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  congr 1
  rw [cylinderMeasure, lintegral_prod _ ((hu.enorm.pow_const (2 : ℝ)).aemeasurable)]
  apply lintegral_congr_ae
  exact Eventually.of_forall (fun t => by
    change eLpNorm (u t) 2 (volume.restrict (Metric.ball z R)) ^ (2 : ℝ) =
      ∫⁻ y in Metric.ball z R, ‖u t y‖ₑ ^ (2 : ℝ)
    have ht : AEStronglyMeasurable (u t) (volume.restrict (Metric.ball z R)) := by
      have h := hu.comp_measurable (measurable_prodMk_left (x := t))
      unfold Function.uncurry Function.comp at h
      exact h.aestronglyMeasurable
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat] using
      (eLpNorm_nnreal_pow_eq_lintegral (ε := ℂ) (p := (2 : ℝ≥0)) (by norm_num) ht))

theorem freeJoint_cylinder_mixedNorm_eq (f : L2) (T R : ℝ) (z : V) :
    TimeHolder.mixedNorm (volume.restrict (Set.Icc (-T) T))
      (volume.restrict (Metric.ball z R)) 2 2 (freeJoint f) =
      eLpNorm (Function.uncurry (freeJoint f)) 2 (cylinderMeasure T R z) :=
  mixedNorm_two_eq_product (u := freeJoint f)
    (by unfold Function.uncurry; exact freeJoint_stronglyMeasurable f) T R z

theorem freeJoint_cylinder_mixedNorm_finite (f : L2) (T R : ℝ) (z : V) :
    TimeHolder.mixedNorm (volume.restrict (Set.Icc (-T) T))
      (volume.restrict (Metric.ball z R)) 2 2 (freeJoint f) ≠ ∞ := by
  rw [freeJoint_cylinder_mixedNorm_eq]
  exact (freeJoint_cylinder_memLp f T R z).eLpNorm_ne_top

theorem freeJoint_cylinder_outer_memLp (f : L2) (T R : ℝ) (z : V) :
    MemLp (fun t => eLpNorm (freeJoint f t) 2 (volume.restrict (Metric.ball z R)))
      2 (volume.restrict (Set.Icc (-T) T)) := by
  change TimeHolder.mixedNorm (volume.restrict (Set.Icc (-T) T))
    (volume.restrict (Metric.ball z R)) 2 2 (freeJoint f) < ∞
  exact lt_top_iff_ne_top.mpr (freeJoint_cylinder_mixedNorm_finite f T R z)

/-- The genuine L2 class of the localized actual representative. -/
def localFreeL2 (T R : ℝ) (z : V) (f : L2) : Lp ℂ 2 (cylinderMeasure T R z) :=
  (freeJoint_cylinder_memLp f T R z).toLp (Function.uncurry (freeJoint f))

theorem localFreeL2_coe (T R : ℝ) (z : V) (f : L2) :
    (localFreeL2 T R z f : (ℝ × V) → ℂ) =ᵐ[cylinderMeasure T R z]
      Function.uncurry (freeJoint f) :=
  (freeJoint_cylinder_memLp f T R z).coeFn_toLp

theorem localFreeL2_norm (T R : ℝ) (z : V) (f : L2) :
    ‖localFreeL2 T R z f‖ =
      (eLpNorm (Function.uncurry (freeJoint f)) 2 (cylinderMeasure T R z)).toReal :=
  Lp.norm_toLp _ _

theorem localFreeL2_norm_sq (T R : ℝ) (z : V) (f : L2) :
    ‖localFreeL2 T R z f‖ ^ 2 =
      ∫ p : ℝ × V, ‖freeJoint f p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z := by
  rw [localFreeL2_norm, eLpNorm_two_toReal_sq (freeJoint_cylinder_memLp f T R z)]
  rfl

/-- Unitarity gives a bounded local operator. This is the finite-window completion map. -/
def localFreeL2CLM {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (z : V) :
    L2 →L[ℂ] Lp ℂ 2 (cylinderMeasure T R z) :=
  LinearMap.mkContinuous
    { toFun := localFreeL2 T R z
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [localFreeL2_coe T R z (f + g),
          localFreeL2_coe T R z f, localFreeL2_coe T R z g,
          freeJoint_cylinder_add_ae f g T R z,
          Lp.coeFn_add (localFreeL2 T R z f) (localFreeL2 T R z g)]
          with p hfg hf hg hs ht
        simp only [Pi.add_apply] at ht
        rw [hfg, ht, hf, hg, hs]
        rfl
      map_smul' := by
        intro a f
        apply Lp.ext
        filter_upwards [localFreeL2_coe T R z (a • f), localFreeL2_coe T R z f,
          freeJoint_cylinder_smul_ae a f T R z,
          Lp.coeFn_smul a (localFreeL2 T R z f)] with p haf hf hs ht
        simp only [Pi.smul_apply] at ht
        change localFreeL2 T R z (a • f) p = (a • localFreeL2 T R z f) p
        rw [haf, ht, hf, hs]
        rfl }
    (Real.sqrt (2 * T)) (fun f => by
      change ‖localFreeL2 T R z f‖ ≤ Real.sqrt (2 * T) * ‖f‖
      rw [localFreeL2_norm]
      exact freeJoint_cylinder_norm_le f hT z)

theorem localFreeL2CLM_apply {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (z : V) (f : L2) :
    localFreeL2CLM hT R z f = localFreeL2 T R z f := rfl

theorem freeJoint_cylinder_integral_tendsto_of_L2 {f : ℕ → L2} {g : L2}
    (hf : Tendsto f atTop (𝓝 g)) {T R : ℝ} (hT : 0 ≤ T) (z : V) :
    Tendsto (fun n => ∫ p : ℝ × V, ‖freeJoint (f n) p.1 p.2‖ ^ 2
      ∂cylinderMeasure T R z) atTop
      (𝓝 (∫ p : ℝ × V, ‖freeJoint g p.1 p.2‖ ^ 2 ∂cylinderMeasure T R z)) := by
  simpa only [Function.comp_def, localFreeL2CLM_apply, localFreeL2_norm_sq] using
    (((localFreeL2CLM hT R z).continuous.tendsto g).comp hf).norm.pow 2

end HartreeF.FreeLocalCompactness
