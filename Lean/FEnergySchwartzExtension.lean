import FEnergyStateWeakGradient
import NoncompactWeakTests

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal RealInnerProductSpace SchwartzMap
namespace HartreeF.EnergySpace
open SobolevStretch

/-- Genuine compact-test weak derivatives extend to every Schwartz test by
the already native spatial-cutoff theorem and actual Holder domains. -/
theorem weak_gradient_schwartz_test {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {f : Space → ℝ} {G : Space → Space} (hf : MemLp f p volume) (hG : MemLp G q volume)
    (hw : HasWeakGradient f G) (ψ : SchwartzMap Space ℝ) (v : Space) :
    (∫ x, f x * fderiv ℝ ψ x v) = -(∫ x, ⟪G x,v⟫ * ψ x) := by
  let := ENNReal.HolderConjugate.inv_one_sub_inv' hp
  let := ENNReal.HolderConjugate.inv_one_sub_inv' hq
  have hGv : MemLp (fun x => ⟪G x,v⟫) q volume := by
    simpa only [Function.comp_def, innerSL_apply_apply, real_inner_comm v] using
      (innerSL ℝ v).comp_memLp' hG
  have hi₀ : Integrable (fun x => f x * ψ x) volume :=
    hf.integrable_mul (ψ.memLp ((1-p⁻¹)⁻¹) volume)
  have hi₁ : Integrable (fun x => f x * fderiv ℝ ψ x v) volume :=
    hf.integrable_mul ((∂_{v} ψ).memLp ((1-p⁻¹)⁻¹) volume)
  have hi₂ : Integrable (fun x => ⟪G x,v⟫ * ψ x) volume :=
    hGv.integrable_mul (ψ.memLp ((1-q⁻¹)⁻¹) volume)
  exact RieszWeakDerivative.weak_gradient_noncompact_test hw (ψ.smooth ⊤) v hi₀ hi₁ hi₂

theorem temperedDistribution_ext_real_tests (T₁ T₂ : TD)
    (h : ∀ ψ : SchwartzMap Space ℝ,
      T₁ (SchwartzMap.postcompCLM Complex.ofRealCLM ψ) =
        T₂ (SchwartzMap.postcompCLM Complex.ofRealCLM ψ)) : T₁ = T₂ := by
  ext φ
  let φR := SchwartzMap.postcompCLM Complex.reCLM φ
  let φI := SchwartzMap.postcompCLM Complex.imCLM φ
  have hdecomp : φ = SchwartzMap.postcompCLM Complex.ofRealCLM φR +
      Complex.I • SchwartzMap.postcompCLM Complex.ofRealCLM φI := by
    ext x
    apply Complex.ext <;> simp [φR, φI, SchwartzMap.postcompCLM_apply, Complex.mul_re,
      Complex.mul_im]
  rw [hdecomp, map_add, map_add, map_smul, map_smul, h φR, h φI]

end HartreeF.EnergySpace
