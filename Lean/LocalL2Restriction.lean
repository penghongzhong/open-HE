import CompactIMSApproximation
import Mathlib.Topology.Order.Compact

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace HartreeF.ComplexIMS
open CutoffApproximation

def localBall (n : ℕ) : Set Space := closedBall 0 (n : ℝ)

theorem localBall_measurable (n : ℕ) : MeasurableSet (localBall n) := isClosed_closedBall.measurableSet

theorem localBall_measure_ne_top (n : ℕ) : volume (localBall n) ≠ ∞ :=
  (isCompact_closedBall (0 : Space) (n : ℝ)).measure_lt_top.ne

theorem localBall_memLp_two {f : Space → ℂ} (hf : MemLp f 6 volume) (n : ℕ) :
    MemLp ((localBall n).indicator f) 2 volume := by
  let : IsFiniteMeasure (volume.restrict (localBall n)) :=
    isFiniteMeasure_restrict.mpr (localBall_measure_ne_top n)
  rw [memLp_indicator_iff_restrict (localBall_measurable n).nullMeasurableSet]
  exact (MemLp.mono_measure Measure.restrict_le_self hf).mono_exponent (by norm_num)

/-- Finite-volume L6-to-local-L2 estimate on the literal fixed ball. -/
theorem localBall_eLpNorm_two_le {f : Space → ℂ} (hf : MemLp f 6 volume) (n : ℕ) :
    eLpNorm ((localBall n).indicator f) 2 volume ≤
      eLpNorm f 6 volume * volume (localBall n) ^ (1 / 3 : ℝ) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (localBall_measurable n).nullMeasurableSet]
  have hm := hf.aestronglyMeasurable.restrict (μ := volume) (s := localBall n)
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (localBall n))
    (p := 2) (q := 6) (by norm_num) hm
  norm_num only [ENNReal.toReal_ofNat, Measure.restrict_apply_univ] at hh
  apply hh.trans
  gcongr
  exact Measure.restrict_le_self

def localL2Constant (n : ℕ) : ℝ := (volume (localBall n)).toReal ^ (1 / 3 : ℝ)

theorem localL2Constant_nonneg (n : ℕ) : 0 ≤ localL2Constant n := by
  unfold localL2Constant
  positivity

theorem localBall_real_norm_le {f : Space → ℂ} (hf : MemLp f 6 volume) (n : ℕ) :
    (eLpNorm ((localBall n).indicator f) 2 volume).toReal ≤
      localL2Constant n * (eLpNorm f 6 volume).toReal := by
  have hfin := ENNReal.mul_ne_top hf.eLpNorm_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) (localBall_measure_ne_top n))
  have hh := ENNReal.toReal_mono hfin (localBall_eLpNorm_two_le hf n)
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, localL2Constant, mul_comm] using hh

/-- Literal fixed-ball restriction, with its produced L2 domain. -/
def localBallLp (n : ℕ) (f : Lp ℂ 6 (volume : Measure Space)) : Lp ℂ 2 (volume : Measure Space) :=
  (localBall_memLp_two (Lp.memLp f) n).toLp ((localBall n).indicator f)

theorem localBallLp_norm (n : ℕ) (f : Lp ℂ 6 (volume : Measure Space)) :
    ‖localBallLp n f‖ = (eLpNorm ((localBall n).indicator f) 2 volume).toReal :=
  Lp.norm_toLp _ _

/-- Restriction is a bounded actual L6-to-L2 map, hence continuous on compact L6 families. -/
theorem localBallLp_lipschitz (n : ℕ) :
    LipschitzWith (localL2Constant n).toNNReal (localBallLp n) := by
  apply LipschitzWith.of_dist_le'
  intro f g
  rw [dist_edist]
  unfold localBallLp
  erw [Lp.edist_toLp_toLp]
  have he : (localBall n).indicator (f : Space → ℂ) - (localBall n).indicator (g : Space → ℂ) =
      (localBall n).indicator ((f : Space → ℂ) - (g : Space → ℂ)) := by
    funext x
    by_cases hx : x ∈ localBall n <;> simp [Set.indicator, hx]
  rw [he, Lp.dist_def]
  exact localBall_real_norm_le ((Lp.memLp f).sub (Lp.memLp g)) n

/-- The local mass is the actual squared L2 integral, not an abstract mass input. -/
theorem localBallLp_mass (n : ℕ) (f : Lp ℂ 6 (volume : Measure Space)) :
    (∫ x in localBall n, ‖f x‖^2) = ‖localBallLp n f‖^2 := by
  rw [localBallLp_norm, ← integral_norm_sq_eq_eLpNorm_sq (localBall_memLp_two (Lp.memLp f) n)]
  have he : (fun x => ‖(localBall n).indicator (f : Space → ℂ) x‖^2) =
      (localBall n).indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x ∈ localBall n <;> simp [Set.indicator, hx]
  rw [he, integral_indicator (localBall_measurable n)]

/-- Concrete finite-ball mass upper bound, requiring no global L2 assumption. -/
theorem localBall_mass_upper {f : Space → ℂ} (hf : MemLp f 6 volume) (n : ℕ) :
    (∫ x in localBall n, ‖f x‖^2) ≤
      (localL2Constant n)^2 * (eLpNorm f 6 volume).toReal^2 := by
  have he : (fun x => ‖(localBall n).indicator f x‖^2) =
      (localBall n).indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x ∈ localBall n <;> simp [Set.indicator, hx]
  have hi := integral_norm_sq_eq_eLpNorm_sq (localBall_memLp_two hf n)
  rw [he, integral_indicator (localBall_measurable n)] at hi
  rw [hi, ← mul_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (localBall_real_norm_le hf n) 2

#print axioms localBall_measurable
#print axioms localBall_measure_ne_top
#print axioms localBall_memLp_two
#print axioms localBall_eLpNorm_two_le
#print axioms localL2Constant_nonneg
#print axioms localBall_real_norm_le
#print axioms localBallLp_norm
#print axioms localBallLp_lipschitz
#print axioms localBallLp_mass
#print axioms localBall_mass_upper
end HartreeF.ComplexIMS
