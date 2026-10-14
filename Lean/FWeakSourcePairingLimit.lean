import FEnergyBanach
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Function.Holder

/-! The actual L^(6/5)/L6 weak integration-by-parts identity extends to
limits of Schwartz tests whose values and directional derivatives both
converge in L6. No extra higher Sobolev density theorem is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.WeakSourcePairing
open EnergySpace

local instance : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
local instance : ENNReal.HolderConjugate (ENNReal.ofReal (6/5 : ℝ)) 6 := by
  have h : Real.HolderTriple (6/5) 6 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

abbrev Source := Lp ℂ (ENNReal.ofReal (6/5 : ℝ)) (volume : Measure V)

def dualPair : Source →L[ℂ] L6 →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing volume
    (ENNReal.ofReal (6/5 : ℝ)) 6

theorem dualPair_eq_integral (f : Source) (h : L6) :
    dualPair f h = ∫ x, f x * h x := by
  exact (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral f h

theorem dualPair_schwartz (f : Source) (φ : Test) :
    dualPair f (φ.toLp 6 volume) = (Lp.toTemperedDistribution f) φ := by
  rw [dualPair_eq_integral, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 6 volume] with x hx
  simp only [hx, smul_eq_mul, mul_comm]

theorem schwartz_source_integration_by_parts (f g : Source) (v : V)
    (hfg : ∂_{v} (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g)
    (φ : Test) :
    dualPair f ((∂_{v} φ).toLp 6 volume) = -dualPair g (φ.toLp 6 volume) := by
  rw [dualPair_schwartz, dualPair_schwartz]
  have h := congrArg (fun T : TD => T φ) hfg
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The limiting test is produced elsewhere by applying a bounded smooth
regularizer to the native Schwartz energy approximation. -/
theorem source_integration_by_parts_of_schwartz_limit
    (f g : Source) (v : V)
    (hfg : ∂_{v} (Lp.toTemperedDistribution f) = Lp.toTemperedDistribution g)
    (φ : ℕ → Test) {h dh : L6}
    (hφ : Tendsto (fun n => (φ n).toLp 6 volume) atTop (𝓝 h))
    (hdφ : Tendsto (fun n => (∂_{v} (φ n)).toLp 6 volume) atTop (𝓝 dh)) :
    (∫ x, f x * dh x) = -(∫ x, g x * h x) := by
  have hl := (dualPair f).continuous.tendsto dh |>.comp hdφ
  have hr := ((dualPair g).continuous.tendsto h |>.comp hφ).neg
  simp only [Function.comp_def] at hl hr
  have he : (fun n => dualPair f ((∂_{v} (φ n)).toLp 6 volume)) =
      (fun n => -dualPair g ((φ n).toLp 6 volume)) := by
    funext n
    exact schwartz_source_integration_by_parts f g v hfg (φ n)
  rw [he] at hl
  simpa only [dualPair_eq_integral] using tendsto_nhds_unique hl hr

#print axioms dualPair
#print axioms dualPair_eq_integral
#print axioms dualPair_schwartz
#print axioms schwartz_source_integration_by_parts
#print axioms source_integration_by_parts_of_schwartz_limit
end HartreeF.WeakSourcePairing
