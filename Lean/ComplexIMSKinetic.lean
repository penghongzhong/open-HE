import ComplexIMSDomains

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter InnerProductSpace
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.ComplexIMS
open SobolevStretch

/-- Pointwise orthogonal rotation cancellation for each real gradient. -/
theorem real_gradient_norm_sq_split (θ f : Space → ℝ) (G : Space → Space) (x : Space) :
    ‖coreGradient θ f G x‖^2 + ‖tailGradient θ f G x‖^2 =
      ‖G x‖^2 + (f x)^2 * ‖gradient θ x‖^2 := by
  simp only [coreGradient, tailGradient, norm_sub_sq_real, norm_add_sq_real,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
    real_inner_smul_right]
  calc
    _ = (Real.sin (θ x)^2 + Real.cos (θ x)^2) *
        (‖G x‖^2 + (f x)^2 * ‖gradient θ x‖^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

/-- The literal C11 complex gradient density satisfies the pointwise IMS identity. -/
theorem complex_gradient_norm_sq_split (θ : Space → ℝ) (u : Space → ℂ)
    (GRe GIm : Space → Space) (x : Space) :
    ‖complexGradient (coreGradient θ (fun y => (u y).re) GRe)
      (coreGradient θ (fun y => (u y).im) GIm) x‖^2 +
    ‖complexGradient (tailGradient θ (fun y => (u y).re) GRe)
      (tailGradient θ (fun y => (u y).im) GIm) x‖^2 =
    ‖complexGradient GRe GIm x‖^2 + ‖u x‖^2 * ‖gradient θ x‖^2 := by
  simp only [complexGradient_norm_sq]
  have hr := real_gradient_norm_sq_split θ (fun y => (u y).re) GRe x
  have hi := real_gradient_norm_sq_split θ (fun y => (u y).im) GIm x
  have hz : ‖u x‖^2 = (u x).re^2 + (u x).im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hz]
  linarith

/-- All three kinetic densities and the IMS error density are truly L1. -/
theorem ims_density_domains {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm) :
    Integrable (fun x => ‖complexGradient GRe GIm x‖^2) volume ∧
    Integrable (fun x => ‖complexGradient (coreGradient θ (fun y => (u y).re) GRe)
      (coreGradient θ (fun y => (u y).im) GIm) x‖^2) volume ∧
    Integrable (fun x => ‖complexGradient (tailGradient θ (fun y => (u y).re) GRe)
      (tailGradient θ (fun y => (u y).im) GIm) x‖^2) volume ∧
    Integrable (fun x => ‖u x‖^2 * ‖gradient θ x‖^2) volume := by
  have hc := core_dotH1 hθ hu
  have ht := tail_dotH1 hθ hu
  exact ⟨kinetic_density_integrable hu.real_gradient_L2 hu.imag_gradient_L2,
    kinetic_density_integrable hc.real_gradient_L2 hc.imag_gradient_L2,
    kinetic_density_integrable ht.real_gradient_L2 ht.imag_gradient_L2,
    error_integrable hθ hu⟩

/-- Actual integrated complex IMS identity. Every integral domain is produced. -/
theorem kinetic_ims {θ : Space → ℝ} {R : ℝ} (hθ : AngleCutoff θ R)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm) :
    kinetic (coreGradient θ (fun x => (u x).re) GRe)
      (coreGradient θ (fun x => (u x).im) GIm) +
    kinetic (tailGradient θ (fun x => (u x).re) GRe)
      (tailGradient θ (fun x => (u x).im) GIm) =
    kinetic GRe GIm + ∫ x, ‖u x‖^2 * ‖gradient θ x‖^2 := by
  obtain ⟨huI, hcI, htI, heI⟩ := ims_density_domains hθ hu
  simp only [kinetic]
  rw [← integral_add hcI htI, ← integral_add huI heI]
  apply integral_congr_ae
  exact Eventually.of_forall (complex_gradient_norm_sq_split θ u GRe GIm)

/-- A single natural interface combines all genuine Sobolev, support and energy outputs. -/
theorem complex_ims_cutoff {θ : Space → ℝ} {R : ℝ}
    (hθ : ContDiff ℝ (⊤ : ENat) θ)
    (hθ0 : ∀ x, 0 ≤ θ x) (hθπ : ∀ x, θ x ≤ Real.pi / 2)
    (hR : 0 < R) (hout : ∀ x, R ≤ ‖x‖ → θ x = Real.pi / 2)
    {u : Space → ℂ} {GRe GIm : Space → Space} (hu : InDotH1 u GRe GIm) :
    InDotH1 (core θ u) (coreGradient θ (fun x => (u x).re) GRe)
      (coreGradient θ (fun x => (u x).im) GIm) ∧
    InDotH1 (tail θ u) (tailGradient θ (fun x => (u x).re) GRe)
      (tailGradient θ (fun x => (u x).im) GIm) ∧
    MemLp (core θ u) 2 volume ∧
    (∀ x, R ≤ ‖x‖ → core θ u x = 0) ∧
    (∀ x, ‖core θ u x‖^2 + ‖tail θ u x‖^2 = ‖u x‖^2) ∧
    Integrable (fun x => ‖u x‖^2 * ‖gradient θ x‖^2) volume ∧
    kinetic (coreGradient θ (fun x => (u x).re) GRe)
      (coreGradient θ (fun x => (u x).im) GIm) +
    kinetic (tailGradient θ (fun x => (u x).re) GRe)
      (tailGradient θ (fun x => (u x).im) GIm) =
    kinetic GRe GIm + ∫ x, ‖u x‖^2 * ‖gradient θ x‖^2 := by
  let hc : AngleCutoff θ R := ⟨hθ, hθ0, hθπ, hR, hout⟩
  exact ⟨core_dotH1 hc hu, tail_dotH1 hc hu, core_L2 hc hu,
    fun _ hx => core_eq_zero_outside hc u hx, norm_sq_split θ u,
    error_integrable hc hu, kinetic_ims hc hu⟩

end HartreeF.ComplexIMS
