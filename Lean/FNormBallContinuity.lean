import FHartreeL2Budget
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcingL2

/-- A finite extended norm-difference coefficient defines a Lipschitz constant. -/
theorem lipschitzOn_of_enorm_sub_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (s : Set E) (L : ℝ≥0∞) (hL : L ≠ ∞)
    (h : ∀ u ∈ s, ∀ v ∈ s, ‖f u-f v‖ₑ ≤ L * ENNReal.ofReal ‖u-v‖) :
    LipschitzOnWith L.toNNReal f s := by
  intro u hu v hv
  simpa only [edist_dist, dist_eq_norm, ENNReal.coe_toNNReal hL, ofReal_norm] using h u hu v hv

/-- Bounded-ball Lipschitz estimates imply continuity on a normed group. -/
theorem continuous_of_lipschitz_norm_balls {E F : Type*}
    [NormedAddCommGroup E] [PseudoEMetricSpace F] (f : E → F)
    (h : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L f {u : E | ‖u‖ ≤ R}) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro v
  obtain ⟨L, hL⟩ := h (‖v‖ + 1)
  have hball : Metric.ball v 1 ⊆ {u : E | ‖u‖ ≤ ‖v‖ + 1} := by
    intro u hu
    have hd : ‖u-v‖ ≤ 1 := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hu).le
    exact (norm_le_norm_sub_add u v).trans (by linarith)
  exact ((hL.mono hball).continuousOn).continuousAt (Metric.ball_mem_nhds v (by norm_num))

/-- An abstract normed-space consumer of the proved Hartree budget. Keeping
metric conversion abstract avoids reducing the concrete closed path graph. -/
theorem lipschitz_norm_ball_of_forcing_budget {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (alpha : ℝ) (ha : 0 < alpha) (ha3 : alpha < 3)
    (f : X → Y) (M S : X → ℝ≥0∞) (D E : X → X → ℝ≥0∞)
    (hbudget : ∃ C : ℝ≥0, ∀ u v, ‖f u-f v‖ₑ ≤
      (C : ℝ≥0∞) * forcingBudget alpha (M u + M v) (S u + S v) (D u v) (E u v))
    (hcommon : ∃ A : ℝ≥0∞, A ≠ ∞ ∧
      (∀ u, M u ≤ A * ENNReal.ofReal ‖u‖ ∧ S u ≤ A * ENNReal.ofReal ‖u‖) ∧
      (∀ u v, D u v ≤ A * ENNReal.ofReal ‖u-v‖ ∧ E u v ≤ A * ENNReal.ofReal ‖u-v‖))
    (R : ℝ) : ∃ L : ℝ≥0, LipschitzOnWith L f {u : X | ‖u‖ ≤ R} := by
  obtain ⟨C, hC⟩ := hbudget
  obtain ⟨A, hA, hsize, hdiff⟩ := hcommon
  let B := A * ENNReal.ofReal R + A * ENNReal.ofReal R
  let L : ℝ≥0∞ := (C : ℝ≥0∞) *
    (B ^ (2 * alpha) * B ^ (4 : ℝ) + B ^ (5 * alpha / 3) * B ^ (4 + alpha / 3)) * A
  have hB : B ≠ ∞ := by dsimp [B]; finiteness
  have ha2 : 0 ≤ 2 * alpha := by positivity
  have ha5 : 0 ≤ 5 * alpha / 3 := by positivity
  have ha4 : 0 ≤ 4 + alpha / 3 := by positivity
  have hL : L ≠ ∞ := by dsimp [L]; finiteness
  refine ⟨L.toNNReal, lipschitzOn_of_enorm_sub_bound f _ L hL ?_⟩
  intro u hu v hv
  have hMu : M u ≤ A * ENNReal.ofReal R :=
    (hsize u).1.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hu))
  have hMv : M v ≤ A * ENNReal.ofReal R :=
    (hsize v).1.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hv))
  have hSu : S u ≤ A * ENNReal.ofReal R :=
    (hsize u).2.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hu))
  have hSv : S v ≤ A * ENNReal.ofReal R :=
    (hsize v).2.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hv))
  have hmono : forcingBudget alpha (M u + M v) (S u + S v) (D u v) (E u v) ≤
      forcingBudget alpha B B (D u v) (E u v) :=
    forcingBudget_mono ha ha3 (add_le_add hMu hMv) (add_le_add hSu hSv) le_rfl le_rfl
  have hb := (hC u v).trans (mul_le_mul' (le_refl (C : ℝ≥0∞)) hmono)
  have hdelta := forcingBudget_le_delta ha ha3 B B (D u v) (E u v)
    (A * ENNReal.ofReal ‖u-v‖) (hdiff u v).1 (hdiff u v).2
  exact (hb.trans (mul_le_mul' le_rfl hdelta)).trans_eq (by dsimp [L]; simp only [mul_assoc])

#print axioms lipschitzOn_of_enorm_sub_bound
#print axioms continuous_of_lipschitz_norm_balls
#print axioms lipschitz_norm_ball_of_forcing_budget
end HartreeF.ForcingL2
