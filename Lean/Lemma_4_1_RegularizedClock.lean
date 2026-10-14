import Lemma_4_1_Clock
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Concrete regularized speed and quarter-power amplitude for Lemma 4.1. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

def regularizedH (h : ℝ → ℝ) (ε : ℝ) (s : ℝ) : ℝ := h s^2+ε

def quarterAmplitude (h : ℝ → ℝ) (ε : ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (regularizedH h ε s))

def clockSpeed (h : ℝ → ℝ) (ε : ℝ) (s : ℝ) : ℝ :=
  (Real.sqrt (regularizedH h ε s))⁻¹

theorem regularizedH_pos (h : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 < regularizedH h ε s := by unfold regularizedH; positivity

theorem quarterAmplitude_pos (h : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 < quarterAmplitude h ε s := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (regularizedH_pos h hε s))

theorem quarterAmplitude_sq (h : ℝ → ℝ) (ε s : ℝ) :
    quarterAmplitude h ε s^2 = Real.sqrt (regularizedH h ε s) :=
  Real.sq_sqrt (Real.sqrt_nonneg _)

theorem quarterAmplitude_fourth (h : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    quarterAmplitude h ε s^4 = regularizedH h ε s := by
  calc
    _ = (quarterAmplitude h ε s^2)^2 := by ring
    _ = _ := by rw [quarterAmplitude_sq,Real.sq_sqrt (regularizedH_pos h hε s).le]

theorem clockSpeed_eq (h : ℝ → ℝ) (ε s : ℝ) :
    clockSpeed h ε s = (quarterAmplitude h ε s^2)⁻¹ := by
  rw [quarterAmplitude_sq]; rfl

theorem regularizedH_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (ε : ℝ) :
    ContDiff ℝ ∞ (regularizedH h ε) := (hh.pow 2).add contDiff_const

theorem quarterAmplitude_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (quarterAmplitude h ε) :=
  ((regularizedH_contDiff hh ε).sqrt (fun s => (regularizedH_pos h hε s).ne')).sqrt
    (fun s => (Real.sqrt_pos.mpr (regularizedH_pos h hε s)).ne')

theorem clockSpeed_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (clockSpeed h ε) :=
  ((regularizedH_contDiff hh ε).sqrt (fun s => (regularizedH_pos h hε s).ne')).inv
    (fun s => (Real.sqrt_pos.mpr (regularizedH_pos h hε s)).ne')

theorem quarterAmplitude_hasDerivAt {h : ℝ → ℝ} {s h' ε : ℝ}
    (hh : HasDerivAt h h' s) (hε : 0 < ε) :
    HasDerivAt (quarterAmplitude h ε) (h s*h'/(2*quarterAmplitude h ε s^3)) s := by
  have hH : HasDerivAt (regularizedH h ε) (2*h s*h') s := by
    change HasDerivAt (fun t => h t^2+ε) (2*h s*h') s
    convert! (hh.pow 2).add_const ε using 1
    ring
  have hd := (hH.sqrt (regularizedH_pos h hε s).ne').sqrt
    (Real.sqrt_pos.mpr (regularizedH_pos h hε s)).ne'
  convert! hd using 1
  have ha := (quarterAmplitude_pos h hε s).ne'
  change h s*h'/(2*quarterAmplitude h ε s^3) =
    (2*h s*h'/(2*Real.sqrt (regularizedH h ε s)))/(2*quarterAmplitude h ε s)
  rw [← quarterAmplitude_sq h ε s]
  field_simp

theorem clockSpeed_lower {h : ℝ → ℝ} {ε M : ℝ} (hε : 0 < ε)
    (hbound : ∀ s,h s^2 ≤ M) :
    0 < (Real.sqrt (M+ε))⁻¹ ∧ ∀ s,(Real.sqrt (M+ε))⁻¹ ≤ clockSpeed h ε s := by
  have hM : 0 ≤ M := (sq_nonneg (h 0)).trans (hbound 0)
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)),?_⟩
  intro s
  apply inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (regularizedH_pos h hε s)) |>.mpr
  exact Real.sqrt_le_sqrt (by unfold regularizedH; linarith [hbound s])

/-- The clock is the integral of the actual inverse square-root speed. -/
def regularizedClock (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) {ε M : ℝ}
    (hε : 0 < ε) (hbound : ∀ s,h s^2 ≤ M) : ℝ ≃ₜ ℝ :=
  clockHomeomorph (clockSpeed h ε) (clockSpeed_contDiff hh hε)
    (clockSpeed_lower hε hbound).1 (clockSpeed_lower hε hbound).2

theorem regularizedClock_hasDerivAt (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    {ε M : ℝ} (hε : 0 < ε) (hbound : ∀ s,h s^2 ≤ M) (s : ℝ) :
    HasDerivAt (regularizedClock h hh hε hbound) (clockSpeed h ε s) s :=
  clock_hasDerivAt (clockSpeed_contDiff hh hε).continuous s

theorem regularizedClock_contDiff (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    {ε M : ℝ} (hε : 0 < ε) (hbound : ∀ s,h s^2 ≤ M) :
    ContDiff ℝ ∞ (regularizedClock h hh hε hbound) :=
  clock_contDiff (clockSpeed_contDiff hh hε)

theorem regularizedClock_inverse_contDiff (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    {ε M : ℝ} (hε : 0 < ε) (hbound : ∀ s,h s^2 ≤ M) :
    ContDiff ℝ ∞ (regularizedClock h hh hε hbound).symm :=
  clock_inverse_contDiff _ _ _ _

/-- The bounded section needed by regularizedClock is derived from the actual
smooth compactly supported three-dimensional function. -/
theorem compact_function_sq_bound {g : Space → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) : ∃ M : ℝ,0 < M ∧ ∀ z,g z^2 ≤ M := by
  obtain ⟨M,hM⟩ := (hc.image (hg.pow 2)).bddAbove
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro z
  by_cases hz : g z = 0
  · simp only [hz,zero_pow (by decide : 2 ≠ 0)]
    exact le_trans zero_le_one (le_max_right _ _)
  · exact (hM (mem_image_of_mem _ (subset_closure hz))).trans (le_max_left _ _)

#print axioms regularizedH_pos
#print axioms quarterAmplitude_pos
#print axioms quarterAmplitude_sq
#print axioms quarterAmplitude_fourth
#print axioms clockSpeed_eq
#print axioms regularizedH_contDiff
#print axioms quarterAmplitude_contDiff
#print axioms clockSpeed_contDiff
#print axioms quarterAmplitude_hasDerivAt
#print axioms clockSpeed_lower
#print axioms regularizedClock_hasDerivAt
#print axioms regularizedClock_contDiff
#print axioms regularizedClock_inverse_contDiff
#print axioms compact_function_sq_bound
end BWork.Kelvin
