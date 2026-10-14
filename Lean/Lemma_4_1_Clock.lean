import Lemma_4_1_TranslatedWeights
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! An actual global clock, its smooth inverse and their derivatives.
All results here use native Mathlib calculus, with no new external interface. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace BWork.Kelvin

def clock (v : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s,v t

theorem clock_zero (v : ℝ → ℝ) : clock v 0 = 0 := by simp [clock]

theorem clock_hasDerivAt {v : ℝ → ℝ} (hv : Continuous v) (s : ℝ) :
    HasDerivAt (clock v) (v s) s :=
  intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _)
    hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

theorem clock_contDiff {v : ℝ → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (clock v) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (clock_hasDerivAt hv.continuous s).differentiableAt,?_⟩
  have he : deriv (clock v) = v := funext (fun s => (clock_hasDerivAt hv.continuous s).deriv)
  rw [he]; exact hv

theorem clock_strictMono {v : ℝ → ℝ} (hv : Continuous v) (hpos : ∀ s,0 < v s) :
    StrictMono (clock v) :=
  strictMono_of_deriv_pos (fun s => by rw [(clock_hasDerivAt hv s).deriv]; exact hpos s)

theorem clock_lower_increment {v : ℝ → ℝ} (hv : Continuous v) {m : ℝ}
    (hlow : ∀ s,m ≤ v s) {s t : ℝ} (hst : s ≤ t) : m*(t-s) ≤ clock v t-clock v s := by
  apply mul_sub_le_image_sub_of_le_deriv (fun x => (clock_hasDerivAt hv x).differentiableAt)
    (fun x => ?_) hst
  rw [(clock_hasDerivAt hv x).deriv]; exact hlow x

theorem clock_tendsto_atTop {v : ℝ → ℝ} (hv : Continuous v) {m : ℝ}
    (hm : 0 < m) (hlow : ∀ s,m ≤ v s) : Tendsto (clock v) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (max 0 (b/m))] with s hs
  have hs₀ : 0 ≤ s := (le_max_left _ _).trans hs
  have hsb : b/m ≤ s := (le_max_right _ _).trans hs
  have hi := clock_lower_increment hv hlow hs₀
  rw [clock_zero,sub_zero,sub_zero] at hi
  exact ((div_le_iff₀ hm).mp hsb).trans (by simpa only [mul_comm] using hi)

theorem clock_tendsto_atBot {v : ℝ → ℝ} (hv : Continuous v) {m : ℝ}
    (hm : 0 < m) (hlow : ∀ s,m ≤ v s) : Tendsto (clock v) atBot atBot := by
  apply tendsto_atBot.mpr
  intro b
  filter_upwards [eventually_le_atBot (min 0 (b/m))] with s hs
  have hs₀ : s ≤ 0 := hs.trans (min_le_left _ _)
  have hsb : s ≤ b/m := hs.trans (min_le_right _ _)
  have hi := clock_lower_increment hv hlow hs₀
  rw [clock_zero] at hi
  have hb := (le_div_iff₀ hm).mp hsb
  nlinarith

def clockHomeomorph (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    {m : ℝ} (hm : 0 < m) (hlow : ∀ s,m ≤ v s) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (clock v)
    (clock_strictMono hv.continuous (fun s => hm.trans_le (hlow s)))
    ((clock_contDiff hv).continuous.surjective (clock_tendsto_atTop hv.continuous hm hlow)
      (clock_tendsto_atBot hv.continuous hm hlow))).toHomeomorph

theorem clockHomeomorph_apply (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    {m : ℝ} (hm : 0 < m) (hlow : ∀ s,m ≤ v s) (s : ℝ) :
    clockHomeomorph v hv hm hlow s = clock v s := rfl

theorem clock_inverse_contDiff (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    {m : ℝ} (hm : 0 < m) (hlow : ∀ s,m ≤ v s) :
    ContDiff ℝ ∞ (clockHomeomorph v hv hm hlow).symm := by
  apply Homeomorph.contDiff_symm_deriv (clockHomeomorph v hv hm hlow)
    (fun s => (hm.trans_le (hlow s)).ne')
    (fun s => clock_hasDerivAt hv.continuous s) (clock_contDiff hv)

theorem clock_inverse_hasDerivAt (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v)
    {m : ℝ} (hm : 0 < m) (hlow : ∀ s,m ≤ v s) (t : ℝ) :
    HasDerivAt (clockHomeomorph v hv hm hlow).symm
      (v ((clockHomeomorph v hv hm hlow).symm t))⁻¹ t := by
  apply HasDerivAt.of_local_left_inverse
    (clockHomeomorph v hv hm hlow).symm.continuous.continuousAt
    (clock_hasDerivAt hv.continuous _) (hm.trans_le (hlow _)).ne'
  exact Eventually.of_forall (clockHomeomorph v hv hm hlow).apply_symm_apply

#print axioms clock_zero
#print axioms clock_hasDerivAt
#print axioms clock_contDiff
#print axioms clock_strictMono
#print axioms clock_lower_increment
#print axioms clock_tendsto_atTop
#print axioms clock_tendsto_atBot
#print axioms clockHomeomorph_apply
#print axioms clock_inverse_contDiff
#print axioms clock_inverse_hasDerivAt
end BWork.Kelvin
