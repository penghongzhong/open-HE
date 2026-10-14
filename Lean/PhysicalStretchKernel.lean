import HartreePhase
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
The literal physical directional stretch kernel. Unlike the spectral kernel,
its exponent is (alpha-3)/2 and no convexity assertion is made. The nonnegative
longitudinal/transverse decomposition is produced from a unit direction. Bounds
are derived uniformly on every positive compact scale interval, including the
zero spatial diagonal, and use only the original physical Riesz kernel.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace
namespace HartreeF.PhysicalStretch

def longitudinalSq (ω z : Space) : ℝ := ⟪ω,z⟫^2
def transverseSq (ω z : Space) : ℝ := ‖z‖^2 - longitudinalSq ω z
def stretchDenominator (ω : Space) (s : ℝ) (z : Space) : ℝ :=
  longitudinalSq ω z + s * transverseSq ω z

def physicalStretchKernel (α c : ℝ) (ω : Space) (s : ℝ) (z : Space) : ℝ :=
  c * s^2 * (stretchDenominator ω s z)^((α-3)/2)

def compactScaleBound (α m M : ℝ) : ℝ := M^2 * (min 1 m)^((α-3)/2)

theorem longitudinalSq_nonneg (ω z : Space) : 0 ≤ longitudinalSq ω z := sq_nonneg _

theorem longitudinalSq_le_norm_sq {ω : Space} (hω : ‖ω‖ = 1) (z : Space) :
    longitudinalSq ω z ≤ ‖z‖^2 := by
  have h := abs_real_inner_le_norm ω z
  rw [hω, one_mul] at h
  unfold longitudinalSq
  nlinarith [sq_abs ⟪ω,z⟫, abs_nonneg ⟪ω,z⟫, norm_nonneg z]

theorem transverseSq_nonneg {ω : Space} (hω : ‖ω‖ = 1) (z : Space) :
    0 ≤ transverseSq ω z := sub_nonneg.mpr (longitudinalSq_le_norm_sq hω z)

theorem directional_square_decomposition (ω z : Space) :
    longitudinalSq ω z + transverseSq ω z = ‖z‖^2 := by
  unfold transverseSq
  ring

/-- Identification with the actual squared norm of the transverse projection. -/
theorem transverseSq_eq_norm_projection {ω : Space} (hω : ‖ω‖ = 1) (z : Space) :
    transverseSq ω z = ‖z - ⟪ω,z⟫ • ω‖^2 := by
  rw [norm_sub_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, hω, mul_one, sq_abs,
    inner_smul_right, real_inner_comm z ω]
  unfold transverseSq longitudinalSq
  rw [real_inner_comm z ω]
  ring

theorem stretchDenominator_lower {ω : Space} (hω : ‖ω‖ = 1)
    {m s : ℝ} (hms : m ≤ s) (z : Space) :
    min 1 m * ‖z‖^2 ≤ stretchDenominator ω s z := by
  have ha := longitudinalSq_nonneg ω z
  have hd := transverseSq_nonneg hω z
  have hm1 := min_le_left (1:ℝ) m
  have hms' := (min_le_right (1:ℝ) m).trans hms
  have h1 := mul_le_mul_of_nonneg_right hm1 ha
  have h2 := mul_le_mul_of_nonneg_right hms' hd
  rw [← directional_square_decomposition ω z]
  unfold stretchDenominator
  nlinarith

theorem stretchDenominator_pos {ω : Space} (hω : ‖ω‖ = 1)
    {s : ℝ} (hs : 0 < s) {z : Space} (hz : z ≠ 0) :
    0 < stretchDenominator ω s z := by
  have hm : 0 < min 1 s := lt_min (by norm_num) hs
  exact (mul_pos hm (sq_pos_of_pos (norm_pos_iff.mpr hz))).trans_le
    (stretchDenominator_lower hω (le_refl s) z)

theorem physicalStretchKernel_measurable (α c : ℝ) (ω : Space) (s : ℝ) :
    Measurable (physicalStretchKernel α c ω s) := by
  have ha : Continuous (longitudinalSq ω) := (continuous_const.inner continuous_id).pow 2
  have hd : Continuous (transverseSq ω) := (continuous_norm.pow 2).sub ha
  exact measurable_const.mul ((ha.add (continuous_const.mul hd)).measurable.pow_const _)

theorem physicalStretchKernel_pair_measurable (α c : ℝ) (ω : Space) (s : ℝ) :
    Measurable (fun q : Space × Space => physicalStretchKernel α c ω s (q.1-q.2)) :=
  (physicalStretchKernel_measurable α c ω s).comp (measurable_fst.sub measurable_snd)

theorem physicalStretchKernel_nonneg {α c : ℝ} (hc : 0 ≤ c)
    {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 ≤ s) (z : Space) :
    0 ≤ physicalStretchKernel α c ω s z := by
  have hd : 0 ≤ stretchDenominator ω s z :=
    add_nonneg (longitudinalSq_nonneg ω z) (mul_nonneg hs (transverseSq_nonneg hω z))
  exact mul_nonneg (mul_nonneg hc (sq_nonneg s)) (Real.rpow_nonneg hd _)

@[simp] theorem physicalStretchKernel_zero {α c : ℝ} (hα3 : α < 3)
    (ω : Space) (s : ℝ) : physicalStretchKernel α c ω s 0 = 0 := by
  have he : (α-3)/2 ≠ 0 := by linarith
  simp [physicalStretchKernel, stretchDenominator, longitudinalSq, transverseSq,
    Real.zero_rpow he]

theorem norm_sq_rpow_half (α : ℝ) (z : Space) :
    (‖z‖^2)^((α-3)/2) = ‖z‖^(α-3) := by
  rw [← Real.rpow_natCast_mul (norm_nonneg z)]
  congr 1
  push_cast
  ring

/-- At scale one the physical kernel is exactly the original Riesz kernel. -/
@[simp] theorem physicalStretchKernel_one (α c : ℝ) (ω : Space) (z : Space) :
    physicalStretchKernel α c ω 1 z = rieszKernel α c z := by
  unfold physicalStretchKernel stretchDenominator
  simp only [one_pow, mul_one, one_mul, directional_square_decomposition,
    norm_sq_rpow_half, rieszKernel]

theorem compactScaleBound_nonneg (α M : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    0 ≤ compactScaleBound α m M :=
  mul_nonneg (sq_nonneg M) (Real.rpow_nonneg (le_min (by norm_num) hm) _)

/-- Uniform domination on every fixed positive compact interval [m,M].
The diagonal case is checked separately; no negative real power is compared at zero. -/
theorem physicalStretchKernel_le_riesz_compact {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1)
    {m M s : ℝ} (hm : 0 < m) (hms : m ≤ s) (hsM : s ≤ M) (z : Space) :
    physicalStretchKernel α c ω s z ≤ compactScaleBound α m M * rieszKernel α c z := by
  by_cases hz : z=0
  · subst z
    rw [physicalStretchKernel_zero hα3]
    unfold compactScaleBound rieszKernel
    positivity
  have hs : 0 < s := hm.trans_le hms
  have hM : 0 < M := hs.trans_le hsM
  have hk : 0 < min 1 m := lt_min (by norm_num) hm
  have hden := stretchDenominator_lower hω hms z
  have hp := Real.rpow_le_rpow_of_nonpos
    (mul_pos hk (sq_pos_of_pos (norm_pos_iff.mpr hz))) hden
    (show (α-3)/2 ≤ 0 by linarith)
  rw [Real.mul_rpow hk.le (sq_nonneg ‖z‖), norm_sq_rpow_half] at hp
  have hs2 : s^2 ≤ M^2 := by nlinarith
  have hc2 := mul_le_mul_of_nonneg_left hs2 hc
  have hpow : 0 ≤ (stretchDenominator ω s z)^((α-3)/2) :=
    Real.rpow_nonneg (stretchDenominator_pos hω hs hz).le _
  unfold physicalStretchKernel compactScaleBound rieszKernel
  calc
    _ ≤ (c*M^2) * (stretchDenominator ω s z)^((α-3)/2) :=
      mul_le_mul_of_nonneg_right hc2 hpow
    _ ≤ (c*M^2) * ((min 1 m)^((α-3)/2) * ‖z‖^(α-3)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hc (sq_nonneg M))
    _ = _ := by ring

theorem physicalStretchKernel_le_riesz {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s) (z : Space) :
    physicalStretchKernel α c ω s z ≤ compactScaleBound α s s * rieszKernel α c z :=
  physicalStretchKernel_le_riesz_compact hα3 hc hω hs (le_refl s) (le_refl s) z

#print axioms longitudinalSq_nonneg
#print axioms longitudinalSq_le_norm_sq
#print axioms transverseSq_nonneg
#print axioms directional_square_decomposition
#print axioms transverseSq_eq_norm_projection
#print axioms stretchDenominator_lower
#print axioms stretchDenominator_pos
#print axioms physicalStretchKernel_measurable
#print axioms physicalStretchKernel_pair_measurable
#print axioms physicalStretchKernel_nonneg
#print axioms physicalStretchKernel_zero
#print axioms norm_sq_rpow_half
#print axioms physicalStretchKernel_one
#print axioms compactScaleBound_nonneg
#print axioms physicalStretchKernel_le_riesz_compact
#print axioms physicalStretchKernel_le_riesz
end HartreeF.PhysicalStretch
