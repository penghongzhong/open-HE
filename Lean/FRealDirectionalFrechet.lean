import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
open Filter Set
open scoped Topology
namespace HartreeF.EnergyVariation

/-- A generic calculus bridge, with no assertion about any particular energy. -/
theorem line_hasDerivAt_everywhere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hline : ∀ x h, HasDerivAt (fun t : ℝ => f (x+t • h)) (D x h) 0)
    (x h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x+s • h)) (D (x+t • h) h) t := by
  have houter : HasDerivAt (fun s : ℝ => f (x+t • h+s • h))
      (D (x+t • h) h) (id t-t) := by simpa using hline (x+t • h) h
  have hd := houter.comp (h := fun s : ℝ => s-t) t ((hasDerivAt_id t).sub_const t)
  simp only [mul_one] at hd
  convert hd using 1
  funext s
  congr 1
  module

/-- Continuous real linear directional derivatives imply the real Frechet derivative.
This general bridge is applied below only after deriving the actual Hartree line formula. -/
theorem hasFDerivAt_of_continuous_directional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hline : ∀ x h, HasDerivAt (fun t : ℝ => f (x+t • h)) (D x h) 0)
    (x : E) (hD : ContinuousAt D x) : HasFDerivAt f (D x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hδbound⟩ := Metric.continuousAt_iff.mp hD ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hhn : ‖h‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  let R : ℝ → ℝ := fun t => f (x+t • h)-f x-t*(D x h)
  let R' : ℝ → ℝ := fun t => (D (x+t • h)-D x) h
  have hd (t : ℝ) : HasDerivAt R (R' t) t := by
    simpa only [R, R', sub_apply, sub_zero, one_mul, Pi.sub_def, id_eq] using
      ((line_hasDerivAt_everywhere hline x h t).sub_const (f x)).sub
        ((hasDerivAt_id t).mul_const (D x h))
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖R' t‖ ≤ ε*‖h‖ := by
    have hp : dist (x+t • h) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg h) ht.2.le).trans_lt hhn
    have he' : ‖D (x+t • h)-D x‖ < ε := by
      simpa only [dist_eq_norm] using hδbound hp
    have he : ‖D (x+t • h)-D x‖ ≤ ε := he'.le
    exact ((D (x+t • h)-D x).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right he (norm_nonneg h))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) hb
  simpa only [R, one_smul, zero_smul, add_zero, zero_mul, sub_zero,
    one_mul, sub_self] using hm

#print axioms line_hasDerivAt_everywhere
#print axioms hasFDerivAt_of_continuous_directional
end HartreeF.EnergyVariation
