import FCompactCrossTemporal

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.CompactCross
open CriticalAffine AffineMixed

/-- Original paper convention: physical center y and profile clock s. -/
def seedFrame (lambda : ℝ) (y : Space) (s w : ℝ) (f : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  parabolicField lambda⁻¹ (-(lambda⁻¹ • y)) s w f

theorem paper_space_map (lambda : ℝ) (y x : Space) :
    affine lambda⁻¹ (-(lambda⁻¹ • y)) x = lambda⁻¹ • (x-y) := by
  simp [affine,sub_eq_add_neg]

theorem paper_space_support_bound {lambda R : ℝ} (hlambda : 0 < lambda) (y x : Space)
    (hx : x ∈ (affine lambda⁻¹ (-(lambda⁻¹ • y))) ⁻¹' Metric.closedBall 0 R) :
    ‖x-y‖ ≤ lambda*R := by
  have hx' : lambda⁻¹*‖x-y‖ ≤ R := by
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right,paper_space_map,norm_smul,
      Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlambda)] using hx
  have hh := mul_le_mul_of_nonneg_left hx' hlambda.le
  simpa only [←mul_assoc,mul_inv_cancel₀ hlambda.ne',one_mul] using hh

theorem paper_time_support_bound {lambda T : ℝ} (hlambda : 0 < lambda) (s t : ℝ)
    (ht : t ∈ (timeAffine lambda⁻¹ s) ⁻¹' Icc (-T) T) :
    |t+lambda^2*s| ≤ lambda^2*T := by
  have he : t+lambda^2*s = lambda^2*timeAffine lambda⁻¹ s t := by
    unfold timeAffine
    field_simp [hlambda.ne']
  rw [he,abs_mul,abs_of_pos (sq_pos_of_pos hlambda)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg lambda)
  exact abs_le.mpr ht

/-- Concrete physical support separation yields a distance lower bound. -/
theorem paper_space_support_separation {lambda mu R D : ℝ} (hlambda : 0 < lambda) (hmu : 0 < mu)
    (y z : Space) (hcenters : D+R*(lambda+mu) ≤ ‖y-z‖) :
    ∀ x ∈ (affine mu⁻¹ (-(mu⁻¹ • z))) ⁻¹' Metric.closedBall 0 R,
      ∀ w ∈ (affine lambda⁻¹ (-(lambda⁻¹ • y))) ⁻¹' Metric.closedBall 0 R, D ≤ ‖x-w‖ := by
  intro x hx w hw
  have hx' := paper_space_support_bound hmu z x hx
  have hw' := paper_space_support_bound hlambda y w hw
  have he : y-z=(y-w)+(w-x)+(x-z) := by abel
  have hn : ‖y-z‖ ≤ ‖w-y‖+‖x-w‖+‖x-z‖ := by
    rw [he]
    calc
      ‖(y-w)+(w-x)+(x-z)‖ ≤ (‖y-w‖+‖w-x‖)+‖x-z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖w-y‖+‖x-w‖+‖x-z‖ := by rw [norm_sub_rev y w,norm_sub_rev w x]
  nlinarith

/-- A sufficiently large physical time-center gap makes the time supports disjoint.
The sign matches theta=-lambda^2*s. -/
theorem paper_time_support_disjoint {lambda mu T : ℝ} (hlambda : 0 < lambda) (hmu : 0 < mu)
    (s r : ℝ) (hgap : T*(lambda^2+mu^2) < |lambda^2*s-mu^2*r|) :
    Disjoint ((timeAffine lambda⁻¹ s) ⁻¹' Icc (-T) T)
      ((timeAffine mu⁻¹ r) ⁻¹' Icc (-T) T) := by
  apply Set.disjoint_left.mpr
  intro t ht hu
  have ht' := paper_time_support_bound hlambda s t ht
  have hu' := paper_time_support_bound hmu r t hu
  have he : lambda^2*s-mu^2*r=(t+lambda^2*s)-(t+mu^2*r) := by ring
  have htri : |lambda^2*s-mu^2*r| ≤ |t+lambda^2*s|+|t+mu^2*r| := by
    rw [he]
    exact abs_sub _ _
  nlinarith

#print axioms paper_space_map
#print axioms paper_space_support_bound
#print axioms paper_time_support_bound
#print axioms paper_space_support_separation
#print axioms paper_time_support_disjoint
end HartreeF.CompactCross
