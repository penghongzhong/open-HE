import PhysicalStretchKernel
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual first derivative and a Riesz majorant on every positive compact
scale interval. The singular spatial diagonal is treated directly, using the
zero-kernel convention valid for alpha<3. No integrated convexity is asserted. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace
namespace HartreeF.PhysicalStretch

def physicalStretchKernelD1 (α c : ℝ) (ω : Space) (s : ℝ) (z : Space) : ℝ :=
  physicalStretchKernel α c ω s z *
    (2/s + ((α-3)/2) * transverseSq ω z / stretchDenominator ω s z)

def compactDerivativeBound (α m M : ℝ) : ℝ :=
  ((2+(3-α)/2)/m) * compactScaleBound α m M

@[simp] theorem physicalStretchKernelD1_zero {α c : ℝ} (hα3 : α < 3)
    (ω : Space) (s : ℝ) : physicalStretchKernelD1 α c ω s 0 = 0 := by
  simp only [physicalStretchKernelD1, physicalStretchKernel_zero hα3, zero_mul]

theorem physicalStretchKernelD1_measurable (α c : ℝ) (ω : Space) (s : ℝ) :
    Measurable (physicalStretchKernelD1 α c ω s) := by
  have ha : Continuous (longitudinalSq ω) := (continuous_const.inner continuous_id).pow 2
  have hd : Continuous (transverseSq ω) := (continuous_norm.pow 2).sub ha
  have hden : Continuous (stretchDenominator ω s) := ha.add (continuous_const.mul hd)
  exact (physicalStretchKernel_measurable α c ω s).mul
    (measurable_const.add ((measurable_const.mul hd.measurable).div hden.measurable))

theorem physicalStretchKernel_hasDerivAt {α c : ℝ} (hα3 : α < 3)
    {ω : Space} (hω : ‖ω‖ = 1) {s : ℝ} (hs : 0 < s) (z : Space) :
    HasDerivAt (fun t => physicalStretchKernel α c ω t z)
      (physicalStretchKernelD1 α c ω s z) s := by
  by_cases hz : z=0
  · subst z
    simp only [physicalStretchKernel_zero hα3, physicalStretchKernelD1_zero hα3]
    exact hasDerivAt_const s 0
  have hden := stretchDenominator_pos hω hs hz
  have h1 := ((hasDerivAt_id s).pow 2).const_mul c
  have h2 := (((hasDerivAt_id s).mul_const (transverseSq ω z)).const_add
    (longitudinalSq ω z)).rpow_const (p := (α-3)/2) (Or.inl hden.ne')
  convert h1.mul h2 using 1
  · rfl
  · unfold physicalStretchKernelD1 physicalStretchKernel stretchDenominator
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, one_mul]
    change 0 < longitudinalSq ω z + s * transverseSq ω z at hden
    rw [Real.rpow_sub_one hden.ne']
    field_simp [hs.ne', hden.ne']

theorem transverse_ratio_le {ω : Space} (hω : ‖ω‖ = 1)
    {m s : ℝ} (hm : 0 < m) (hms : m ≤ s) {z : Space} (hz : z ≠ 0) :
    transverseSq ω z / stretchDenominator ω s z ≤ 1/m := by
  have hden := stretchDenominator_pos hω (hm.trans_le hms) hz
  apply (div_le_div_iff₀ hden hm).mpr
  have ha := longitudinalSq_nonneg ω z
  have hd := transverseSq_nonneg hω z
  have h := mul_le_mul_of_nonneg_right hms hd
  unfold stretchDenominator
  nlinarith

theorem compactDerivativeBound_nonneg {α m M : ℝ} (hα3 : α < 3) (hm : 0 < m) :
    0 ≤ compactDerivativeBound α m M := by
  unfold compactDerivativeBound
  apply mul_nonneg _ (compactScaleBound_nonneg α M hm.le)
  exact div_nonneg (by linarith) hm.le

/-- The derivative is dominated by a fixed multiple of the original Riesz kernel,
uniformly for m<=s<=M, with no exceptional spatial points. -/
theorem physicalStretchKernelD1_abs_le_riesz_compact {α c : ℝ} (hα3 : α < 3)
    (hc : 0 ≤ c) {ω : Space} (hω : ‖ω‖ = 1)
    {m M s : ℝ} (hm : 0 < m) (hms : m ≤ s) (hsM : s ≤ M) (z : Space) :
    |physicalStretchKernelD1 α c ω s z| ≤
      compactDerivativeBound α m M * rieszKernel α c z := by
  by_cases hz : z=0
  · subst z
    rw [physicalStretchKernelD1_zero hα3, abs_zero]
    exact mul_nonneg (compactDerivativeBound_nonneg hα3 hm) (by unfold rieszKernel; positivity)
  have hs := hm.trans_le hms
  have hden := stretchDenominator_pos hω hs hz
  have hd := transverseSq_nonneg hω z
  have hr := transverse_ratio_le hω hm hms hz
  have h2 : 2/s ≤ 2/m := div_le_div_of_nonneg_left (by norm_num) hm hms
  have he : (α-3)/2 < 0 := by linarith
  have hfac : |2/s + ((α-3)/2) * transverseSq ω z / stretchDenominator ω s z| ≤
      (2+(3-α)/2)/m := by
    calc
      _ ≤ |2/s| + |((α-3)/2) * transverseSq ω z / stretchDenominator ω s z| := abs_add_le _ _
      _ = 2/s + ((3-α)/2) * (transverseSq ω z / stretchDenominator ω s z) := by
        rw [abs_of_pos (div_pos (by norm_num) hs), mul_div_assoc, abs_mul,
          abs_of_neg he, abs_of_nonneg (div_nonneg hd hden.le)]
        ring
      _ ≤ 2/m + ((3-α)/2) * (1/m) :=
        add_le_add h2 (mul_le_mul_of_nonneg_left hr (by linarith))
      _ = _ := by ring
  have hk0 := physicalStretchKernel_nonneg (α := α) hc hω hs.le z
  have hk := physicalStretchKernel_le_riesz_compact hα3 hc hω hm hms hsM z
  have hcoef : 0 ≤ (2+(3-α)/2)/m := div_nonneg (by linarith) hm.le
  unfold physicalStretchKernelD1
  rw [abs_mul, abs_of_nonneg hk0]
  calc
    _ ≤ physicalStretchKernel α c ω s z * ((2+(3-α)/2)/m) :=
      mul_le_mul_of_nonneg_left hfac hk0
    _ ≤ (compactScaleBound α m M * rieszKernel α c z) * ((2+(3-α)/2)/m) :=
      mul_le_mul_of_nonneg_right hk hcoef
    _ = _ := by unfold compactDerivativeBound; ring

/-- Exact s=1 physical pressure coefficient, including the zero diagonal. -/
theorem physicalStretchKernelD1_one {α c : ℝ} (hα3 : α < 3)
    (ω : Space) (z : Space) :
    physicalStretchKernelD1 α c ω 1 z = rieszKernel α c z *
      ((1+α)/2 + ((3-α)/2) * longitudinalSq ω z / ‖z‖^2) := by
  by_cases hz : z=0
  · subst z
    have he : α-3 ≠ 0 := by linarith
    simp [physicalStretchKernelD1_zero hα3, rieszKernel, Real.zero_rpow he]
  have hn : ‖z‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  unfold physicalStretchKernelD1
  rw [physicalStretchKernel_one]
  congr 1
  unfold stretchDenominator transverseSq
  simp only [one_mul, div_one]
  field_simp
  ring

#print axioms physicalStretchKernelD1_zero
#print axioms physicalStretchKernelD1_measurable
#print axioms physicalStretchKernel_hasDerivAt
#print axioms transverse_ratio_le
#print axioms compactDerivativeBound_nonneg
#print axioms physicalStretchKernelD1_abs_le_riesz_compact
#print axioms physicalStretchKernelD1_one
end HartreeF.PhysicalStretch
