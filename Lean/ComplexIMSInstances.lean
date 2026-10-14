import ComplexIMSKinetic
import CutoffGeometry

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ComplexIMS
open SobolevStretch

/-- An explicit angle made from the previously constructed expanding smooth bump. -/
def cutoffAngle (n : ℕ) (x : Space) : ℝ :=
  (Real.pi / 2) * (1 - CutoffApproximation.cutoff n x)

theorem cutoffAngle_valid (n : ℕ) :
    AngleCutoff (cutoffAngle n) (2 * ((n : ℝ) + 1)) := by
  refine ⟨contDiff_const.mul (contDiff_const.sub (CutoffApproximation.cutoff_smooth n)),
    ?_, ?_, by positivity, ?_⟩
  · intro x
    unfold cutoffAngle
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (CutoffApproximation.cutoff_le_one n x))
  · intro x
    unfold cutoffAngle
    have hp := Real.pi_pos
    have hc := CutoffApproximation.cutoff_nonneg n x
    nlinarith
  · intro x hx
    simp only [cutoffAngle, CutoffApproximation.cutoff_eq_zero n hx, sub_zero, mul_one]

theorem cutoffAngle_zero_inside (n : ℕ) {x : Space} (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    cutoffAngle n x = 0 := by
  simp only [cutoffAngle, CutoffApproximation.cutoff_eq_one n hx, sub_self, mul_zero]

theorem core_cutoffAngle_eq_self_inside (n : ℕ) (u : Space → ℂ)
    {x : Space} (hx : ‖x‖ ≤ (n : ℝ) + 1) : core (cutoffAngle n) u x = u x := by
  simp only [core, cutoffAngle_zero_inside n hx, Real.cos_zero, one_smul]

theorem tail_cutoffAngle_eq_zero_inside (n : ℕ) (u : Space → ℂ)
    {x : Space} (hx : ‖x‖ ≤ (n : ℝ) + 1) : tail (cutoffAngle n) u x = 0 := by
  simp only [tail, cutoffAngle_zero_inside n hx, Real.sin_zero, zero_smul]

/-- Every n gives an actual complex IMS splitting with produced Sobolev domains. -/
theorem cutoffAngle_ims {u : Space → ℂ} {GRe GIm : Space → Space}
    (hu : InDotH1 u GRe GIm) (n : ℕ) :
    InDotH1 (core (cutoffAngle n) u)
      (coreGradient (cutoffAngle n) (fun x => (u x).re) GRe)
      (coreGradient (cutoffAngle n) (fun x => (u x).im) GIm) ∧
    InDotH1 (tail (cutoffAngle n) u)
      (tailGradient (cutoffAngle n) (fun x => (u x).re) GRe)
      (tailGradient (cutoffAngle n) (fun x => (u x).im) GIm) ∧
    MemLp (core (cutoffAngle n) u) 2 volume ∧
    kinetic (coreGradient (cutoffAngle n) (fun x => (u x).re) GRe)
      (coreGradient (cutoffAngle n) (fun x => (u x).im) GIm) +
    kinetic (tailGradient (cutoffAngle n) (fun x => (u x).re) GRe)
      (tailGradient (cutoffAngle n) (fun x => (u x).im) GIm) =
    kinetic GRe GIm + ∫ x, ‖u x‖^2 * ‖gradient (cutoffAngle n) x‖^2 := by
  exact ⟨core_dotH1 (cutoffAngle_valid n) hu, tail_dotH1 (cutoffAngle_valid n) hu,
    core_L2 (cutoffAngle_valid n) hu, kinetic_ims (cutoffAngle_valid n) hu⟩

/-- Both multipliers lie in [0,1], needed by the nonlocal energy consumers. -/
theorem AngleCutoff.trigonometric_range {θ : Space → ℝ} {R : ℝ}
    (hθ : AngleCutoff θ R) (x : Space) :
    0 ≤ Real.cos (θ x) ∧ Real.cos (θ x) ≤ 1 ∧
    0 ≤ Real.sin (θ x) ∧ Real.sin (θ x) ≤ 1 := by
  refine ⟨Real.cos_nonneg_of_mem_Icc ⟨?_, hθ.le_half_pi x⟩,
    Real.cos_le_one _, Real.sin_nonneg_of_nonneg_of_le_pi (hθ.nonneg x) ?_,
    Real.sin_le_one _⟩
  · linarith [hθ.nonneg x, Real.pi_pos]
  · linarith [hθ.le_half_pi x, Real.pi_pos]

/-- The three sixth-power densities are integrable from the produced L6 domains. -/
theorem sixth_power_domains {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm) :
    Integrable (fun x => ‖u x‖^6) volume ∧
    Integrable (fun x => ‖core θ u x‖^6) volume ∧
    Integrable (fun x => ‖tail θ u x‖^6) volume :=
  ⟨hu.function_L6.integrable_norm_pow (by decide : (6 : ℕ) ≠ 0),
    (core_dotH1 hθ hu).function_L6.integrable_norm_pow (by decide : (6 : ℕ) ≠ 0),
    (tail_dotH1 hθ hu).function_L6.integrable_norm_pow (by decide : (6 : ℕ) ≠ 0)⟩

end HartreeF.ComplexIMS
