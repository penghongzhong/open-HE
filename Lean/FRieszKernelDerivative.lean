import ClassicalWeakGradient
import LocallyDominatedWeakClosure
import RieszKernelTestCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Genuine weak derivative of the singular Riesz kernel on the actual Euclidean R3.
This source uses positive smooth
regularizations and locally dominated convergence of weak gradients.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped RealInnerProductSpace Topology
namespace HartreeF.RieszKernelDerivative
open SobolevStretch RieszWeakDerivative WeakHartreeProduct

/-- The value at the origin is zero because the vector factor is zero. -/
def rieszKernelGradient (α c : ℝ) (z : Space) : Space :=
  (c * (α - 3) * ‖z‖ ^ (α - 5)) • z

@[simp] theorem rieszKernelGradient_zero (α c : ℝ) :
    rieszKernelGradient α c 0 = 0 := by
  simp [rieszKernelGradient]

theorem rieszKernelGradient_measurable (α c : ℝ) :
    Measurable (rieszKernelGradient α c) := by
  exact (measurable_const.mul
    (continuous_norm.measurable.pow_const (α - 5))).smul measurable_id

private theorem norm_sq_rpow_half (z : Space) (p : ℝ) :
    (‖z‖ ^ 2) ^ (p / 2) = ‖z‖ ^ p := by
  calc
    (‖z‖ ^ 2) ^ (p / 2) = (‖z‖ ^ (2 : ℝ)) ^ (p / 2) := by
      rw [Real.rpow_two]
    _ = ‖z‖ ^ ((2 : ℝ) * (p / 2)) :=
      (Real.rpow_mul (norm_nonneg z) _ _).symm
    _ = ‖z‖ ^ p := by congr 1; ring

theorem rieszKernelGradient_norm {α c : ℝ} (hα : α < 3) (hc : 0 < c)
    (z : Space) :
    ‖rieszKernelGradient α c z‖ = c * (3 - α) * ‖z‖ ^ (α - 4) := by
  by_cases hz : z = 0
  · subst z
    simp [Real.zero_rpow (by linarith : α - 4 ≠ 0)]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have habs : |c * (α - 3) * ‖z‖ ^ (α - 5)| =
      c * (3 - α) * ‖z‖ ^ (α - 5) := by
    rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_neg (sub_neg.mpr hα),
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    ring
  rw [rieszKernelGradient, norm_smul, Real.norm_eq_abs, habs]
  calc
    c * (3 - α) * ‖z‖ ^ (α - 5) * ‖z‖ =
        c * (3 - α) * (‖z‖ ^ (α - 5) * ‖z‖) := by ring
    _ = c * (3 - α) * ‖z‖ ^ (α - 4) := by
      rw [← Real.rpow_add_one hn]
      congr 2
      ring

/-- Exact norm identification with the lower-order positive Riesz kernel. -/
theorem rieszKernelGradient_norm_eq_lowerOrder {α c c' : ℝ}
    (hα : α < 3) (hc : 0 < c) (hc' : 0 < c') (z : Space) :
    ‖rieszKernelGradient α c z‖ =
      (c * (3 - α) / c') * rieszKernel (α - 1) c' z := by
  rw [rieszKernelGradient_norm hα hc, rieszKernel,
    show α - 1 - 3 = α - 4 by ring]
  field_simp [hc'.ne']

/-- The pointwise estimate used by the later convolution derivative transfer. -/
theorem rieszKernelGradient_norm_le_lowerOrder {α c c' : ℝ}
    (hα : α < 3) (hc : 0 < c) (hc' : 0 < c') (z : Space) :
    ‖rieszKernelGradient α c z‖ ≤
      (c * (3 - α) / c') * rieszKernel (α - 1) c' z :=
  (rieszKernelGradient_norm_eq_lowerOrder hα hc hc' z).le

theorem rieszKernelGradient_locallyIntegrable {α c : ℝ}
    (hα1 : 1 < α) (hα3 : α < 3) (hc : 0 < c) :
    LocallyIntegrable (rieszKernelGradient α c) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := c * (3 - α)) (α := 4 - α)
    (by simp [Space])
    (by simp only [Space, finrank_euclideanSpace_fin, Nat.cast_ofNat]; linarith)
  · filter_upwards [] with z
    rw [rieszKernelGradient_norm hα3 hc, show -(4 - α) = α - 4 by ring]
  · exact (rieszKernelGradient_measurable α c).aestronglyMeasurable

/-- The local integrability threshold is sharp throughout α < 3 and c > 0. -/
theorem rieszKernelGradient_locallyIntegrable_iff {α c : ℝ}
    (hα3 : α < 3) (hc : 0 < c) :
    LocallyIntegrable (rieszKernelGradient α c) volume ↔ 1 < α := by
  refine ⟨?_, fun hα1 => rieszKernelGradient_locallyIntegrable hα1 hα3 hc⟩
  intro hG
  have hC : c * (3 - α) ≠ 0 := ne_of_gt (mul_pos hc (sub_pos.mpr hα3))
  have hball : IntegrableOn (rieszKernelGradient α c) (Metric.ball (0 : Space) 1) volume :=
    (hG.integrableOn_isCompact (isCompact_closedBall (0 : Space) 1)).mono_set
      Metric.ball_subset_closedBall
  have hn : IntegrableOn (fun z : Space => c * (3 - α) * ‖z‖ ^ (α - 4))
      (Metric.ball (0 : Space) 1) volume := by
    simpa only [IntegrableOn, rieszKernelGradient_norm hα3 hc] using hball.norm
  have hp : IntegrableOn (fun z : Space => ‖z‖ ^ (α - 4))
      (Metric.ball (0 : Space) 1) volume := by
    have h := hn.const_mul (c * (3 - α))⁻¹
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hC, one_mul] using h
  have hr := (integrableOn_fun_norm_addHaar (E := Space) volume
    (f := fun r : ℝ => r ^ (α - 4)) (r := 1)).mp hp
  have hr' : IntegrableOn (fun r : ℝ => r ^ (α - 2)) (Ioo 0 1) volume := by
    apply hr.congr_fun _ measurableSet_Ioo
    intro r hr
    simp only [Space, finrank_euclideanSpace_fin, smul_eq_mul]
    change r ^ 2 * r ^ (α - 4) = r ^ (α - 2)
    rw [← Real.rpow_two, ← Real.rpow_add hr.1]
    congr 1
    ring
  have ht := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mp hr'
  linarith

/-- ε is added to the squared radius; it is strictly positive below. -/
def regularizedRieszKernel (α c ε : ℝ) (z : Space) : ℝ :=
  c * (‖z‖ ^ 2 + ε) ^ ((α - 3) / 2)

def regularizedRieszGradient (α c ε : ℝ) (z : Space) : Space :=
  (c * (α - 3) * (‖z‖ ^ 2 + ε) ^ ((α - 5) / 2)) • z

private theorem regularizedRieszKernel_hasFDerivAt (α c : ℝ) {ε : ℝ}
    (hε : 0 < ε) (z : Space) :
    HasFDerivAt (regularizedRieszKernel α c ε)
      ((c * (α - 3) * (‖z‖ ^ 2 + ε) ^ ((α - 5) / 2)) • innerSL ℝ z) z := by
  have hp : 0 < ‖z‖ ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have h := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const ε).rpow_const
    (p := (α - 3) / 2) (Or.inl hp.ne')).const_mul c
  convert h using 1 <;> try rfl
  ext v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, add_apply, two_smul]
  rw [show (α - 3) / 2 - 1 = (α - 5) / 2 by ring]
  ring

theorem regularizedRieszKernel_hasWeakGradient (α c : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    HasWeakGradient (regularizedRieszKernel α c ε) (regularizedRieszGradient α c ε) := by
  apply hasWeakGradient_of_differentiable
    (fun z => (regularizedRieszKernel_hasFDerivAt α c hε z).differentiableAt)
  · have hb : Continuous (fun z : Space => ‖z‖ ^ 2 + ε) :=
      (continuous_norm.pow 2).add continuous_const
    have hp : Continuous (fun z : Space => (‖z‖ ^ 2 + ε) ^ ((α - 5) / 2)) :=
      hb.rpow_const (fun z => Or.inl
        (ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε)))
    exact (continuous_const.mul hp).smul continuous_id
  · intro z v
    rw [(regularizedRieszKernel_hasFDerivAt α c hε z).fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      regularizedRieszGradient, real_inner_smul_left]

private theorem regularizedRieszKernel_norm_le {α c ε : ℝ}
    (hα3 : α < 3) (hc : 0 < c) (hε : 0 < ε) {z : Space} (hz : z ≠ 0) :
    ‖regularizedRieszKernel α c ε z‖ ≤ rieszKernel α c z := by
  have hr : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hp : 0 ≤ (‖z‖ ^ 2 + ε) ^ ((α - 3) / 2) :=
    Real.rpow_nonneg (by positivity) _
  rw [regularizedRieszKernel, Real.norm_eq_abs, abs_mul, abs_of_pos hc, abs_of_nonneg hp]
  calc
    c * (‖z‖ ^ 2 + ε) ^ ((α - 3) / 2) ≤
        c * (‖z‖ ^ 2) ^ ((α - 3) / 2) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      exact Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
    _ = rieszKernel α c z := by rw [norm_sq_rpow_half]; rfl

private theorem regularizedRieszGradient_norm_le {α c ε : ℝ}
    (hα3 : α < 3) (hc : 0 < c) (hε : 0 < ε) {z : Space} (hz : z ≠ 0) :
    ‖regularizedRieszGradient α c ε z‖ ≤ rieszKernel (α - 1) (c * (3 - α)) z := by
  have hr : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hp : 0 ≤ (‖z‖ ^ 2 + ε) ^ ((α - 5) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hC : 0 ≤ c * (3 - α) := mul_nonneg hc.le (by linarith)
  have habs : |c * (α - 3) * (‖z‖ ^ 2 + ε) ^ ((α - 5) / 2)| =
      c * (3 - α) * (‖z‖ ^ 2 + ε) ^ ((α - 5) / 2) := by
    rw [abs_mul, abs_mul, abs_of_pos hc, abs_of_neg (sub_neg.mpr hα3), abs_of_nonneg hp]
    ring
  rw [regularizedRieszGradient, norm_smul, Real.norm_eq_abs, habs]
  calc
    c * (3 - α) * (‖z‖ ^ 2 + ε) ^ ((α - 5) / 2) * ‖z‖ ≤
        c * (3 - α) * (‖z‖ ^ 2) ^ ((α - 5) / 2) * ‖z‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow_of_nonpos hr (by linarith) (by linarith)
    _ = c * (3 - α) * ‖z‖ ^ (α - 4) := by
      rw [norm_sq_rpow_half, mul_assoc, ← Real.rpow_add_one (norm_ne_zero_iff.mpr hz)]
      congr 2
      ring
    _ = rieszKernel (α - 1) (c * (3 - α)) z := by
      rw [rieszKernel]
      congr 2
      ring

/-- Smooth radial regularizations produce the genuine singular weak derivative.
Neither an integration-by-parts identity nor a kernel-gradient assumption is an input. -/
theorem rieszKernel_hasWeakGradient {α c : ℝ}
    (hα1 : 1 < α) (hα3 : α < 3) (hc : 0 < c) :
    HasWeakGradient (rieszKernel α c) (rieszKernelGradient α c) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  apply hasWeakGradient_of_locally_dominated_limit
    (fn := fun n => regularizedRieszKernel α c (ε n))
    (Gn := fun n => regularizedRieszGradient α c (ε n))
    (M := rieszKernel α c) (N := rieszKernel (α - 1) (c * (3 - α)))
    (rieszKernel_locallyIntegrable (by linarith) c)
    (rieszKernelGradient_locallyIntegrable hα1 hα3 hc)
    (rieszKernel_locallyIntegrable (by linarith) c)
    (rieszKernel_locallyIntegrable (by linarith) (c * (3 - α)))
  · intro n
    exact regularizedRieszKernel_hasWeakGradient α c (hε n)
  · intro n
    filter_upwards [volume.ae_ne (0 : Space)] with z hz
    exact regularizedRieszKernel_norm_le hα3 hc (hε n) hz
  · intro n
    filter_upwards [volume.ae_ne (0 : Space)] with z hz
    exact regularizedRieszGradient_norm_le hα3 hc (hε n) hz
  · filter_upwards [volume.ae_ne (0 : Space)] with z hz
    have hb : Tendsto (fun n => ‖z‖ ^ 2 + ε n) atTop (𝓝 (‖z‖ ^ 2)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := ‖z‖ ^ 2)).add hεt
    have hp := (Real.continuousAt_rpow_const (‖z‖ ^ 2) ((α - 3) / 2)
      (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)))).tendsto.comp hb
    simpa only [Function.comp_def, regularizedRieszKernel, rieszKernel, norm_sq_rpow_half] using hp.const_mul c
  · filter_upwards [volume.ae_ne (0 : Space)] with z hz
    have hb : Tendsto (fun n => ‖z‖ ^ 2 + ε n) atTop (𝓝 (‖z‖ ^ 2)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := ‖z‖ ^ 2)).add hεt
    have hp := (Real.continuousAt_rpow_const (‖z‖ ^ 2) ((α - 5) / 2)
      (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)))).tendsto.comp hb
    simpa only [Function.comp_def, regularizedRieszGradient, rieszKernelGradient, norm_sq_rpow_half] using
      (hp.const_mul (c * (α - 3))).smul (tendsto_const_nhds (x := z))

#print axioms rieszKernelGradient_norm_eq_lowerOrder
#print axioms rieszKernelGradient_locallyIntegrable_iff
#print axioms regularizedRieszKernel_hasWeakGradient
#print axioms rieszKernel_hasWeakGradient
end HartreeF.RieszKernelDerivative
