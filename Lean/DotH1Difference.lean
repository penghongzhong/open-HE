import ActualIMSCoreMassNeighborhood
import SharpOrdinaryInterfaces

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.DotH1Topology
open SobolevStretch ComplexIMS SharpOrdinary

/-- Both distributional test integrals of the actual difference have genuine L1 domains. -/
theorem weak_gradient_sub_test_integrable {u v : Space → ℝ} {U V : Space → Space}
    (hu : HasWeakGradient u U) (hv : HasWeakGradient v V) {φ : Space → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (w : Space) :
    Integrable (fun x => (u x-v x) * fderiv ℝ φ x w) volume ∧
    Integrable (fun x => ⟪U x-V x,w⟫ * φ x) volume := by
  have hiu := hu.test_integrable hφ hc w
  have hiv := hv.test_integrable hφ hc w
  have h1 : Integrable (fun x => u x * fderiv ℝ φ x w-v x * fderiv ℝ φ x w) volume :=
    hiu.1.sub hiv.1
  have h2 : Integrable (fun x => ⟪U x,w⟫ * φ x-⟪V x,w⟫ * φ x) volume :=
    hiu.2.sub hiv.2
  exact ⟨by simpa only [sub_mul] using h1,
    by simpa only [inner_sub_left, sub_mul] using h2⟩

/-- Subtraction of true weak gradients, with every integration-by-parts domain produced. -/
theorem weak_gradient_sub {u v : Space → ℝ} {U V : Space → Space}
    (hu : HasWeakGradient u U) (hv : HasWeakGradient v V) :
    HasWeakGradient (fun x => u x-v x) (fun x => U x-V x) := by
  refine ⟨hu.function_local.sub hv.function_local, hu.gradient_local.sub hv.gradient_local, ?_⟩
  intro w φ hφ hc
  have hiu := hu.test_integrable hφ hc w
  have hiv := hv.test_integrable hφ hc w
  simp only [sub_mul, inner_sub_left, integral_sub hiu.1 hiv.1,
    integral_sub hiu.2 hiv.2, hu.integration_by_parts w φ hφ hc,
    hv.integration_by_parts w φ hφ hc]
  ring

/-- The actual complex difference remains homogeneous Sobolev, with literal gradient differences. -/
theorem inDotH1_sub {u v : Space → ℂ} {URe UIm VRe VIm : Space → Space}
    (hu : InDotH1 u URe UIm) (hv : InDotH1 v VRe VIm) :
    InDotH1 (fun x => u x-v x) (fun x => URe x-VRe x) (fun x => UIm x-VIm x) := by
  refine ⟨hu.function_L6.sub hv.function_L6, hu.real_gradient_L2.sub hv.real_gradient_L2,
    hu.imag_gradient_L2.sub hv.imag_gradient_L2, ?_, ?_⟩
  · simpa only [Complex.sub_re] using weak_gradient_sub hu.real_weak hv.real_weak
  · simpa only [Complex.sub_im] using weak_gradient_sub hu.imag_weak hv.imag_weak

/-- The sharp ordinary inequality applied to the produced actual difference. -/
theorem function_difference_sobolev_sq (hS : SharpOrdinarySobolev)
    (f g : HomogeneousData) :
    (eLpNorm (fun x => f.u x-g.u x) 6 volume).toReal^2 ≤
      sharpSobolevConstant *
        ((eLpNorm (fun x => f.realGradient x-g.realGradient x) 2 volume).toReal^2 +
          (eLpNorm (fun x => f.imagGradient x-g.imagGradient x) 2 volume).toReal^2) := by
  have hd := inDotH1_sub f.domain g.domain
  have hs := hS.bound hd
  rw [kinetic_eq_sum hd.real_gradient_L2 hd.imag_gradient_L2,
    integral_norm_sq_eq_eLpNorm_sq hd.real_gradient_L2,
    integral_norm_sq_eq_eLpNorm_sq hd.imag_gradient_L2] at hs
  exact hs

/-- The concrete Lp quotient distance is the finite seminorm of the supplied pointwise difference. -/
theorem toLp_distance {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f g : Space → E} (hf : MemLp f p volume) (hg : MemLp g p volume) :
    dist (hf.toLp f) (hg.toLp g) = (eLpNorm (fun x => f x-g x) p volume).toReal := by
  rw [dist_edist]
  erw [Lp.edist_toLp_toLp]
  rfl

#print axioms weak_gradient_sub_test_integrable
#print axioms weak_gradient_sub
#print axioms inDotH1_sub
#print axioms function_difference_sobolev_sq
#print axioms toLp_distance
end HartreeF.DotH1Topology
