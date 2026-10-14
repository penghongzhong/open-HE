import FEnergyWeakTestBridge
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal
namespace HartreeF.EnergySpace

theorem compact_test_derivative_support (φ : V → ℝ) (hc : HasCompactSupport φ) (v : V) :
    HasCompactSupport (fun x => fderiv ℝ φ x v) :=
  (hc.fderiv ℝ).comp_left (g := fun L : V →L[ℝ] ℝ => L v) (by rfl)

theorem energyState_projected_coordinate_test (u : EnergyState) (j : Fin 3)
    (L : ℂ →L[ℝ] ℝ) (φ : V → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    (∫ x, L (energyValue u x) * fderiv ℝ φ x (coordinate j)) =
      -(∫ x, L (energyGradient j u x) * φ x) := by
  let ψ : V → ℂ := fun x => Complex.ofRealCLM (φ x)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp hφ
  have hcψ : HasCompactSupport ψ := hc.comp_left (g := Complex.ofRealCLM) (map_zero _)
  have hd (x : V) : fderiv ℝ ψ x (coordinate j) =
      Complex.ofRealCLM (fderiv ℝ φ x (coordinate j)) := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp x
      ((hφ.differentiable (by simp) x).hasFDerivAt)
    change fderiv ℝ (Complex.ofRealCLM ∘ φ) x (coordinate j) = _
    rw [h.fderiv]
    rfl
  have hi₁ : Integrable (fun x => fderiv ℝ φ x (coordinate j) • energyValue u x) volume :=
    ((Lp.memLp (energyValue u)).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (compact_test_derivative_support φ hc (coordinate j))
  have hi₂ : Integrable (fun x => φ x • energyGradient j u x) volume :=
    ((Lp.memLp (energyGradient j u)).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have h := energyState_compact_test u j ψ hψ hcψ
  simp only [hd] at h
  simp only [ψ, Complex.ofRealCLM_apply, ← Complex.real_smul] at h
  have hp := congrArg L h
  rw [map_neg, ← L.integral_comp_comm hi₁, ← L.integral_comp_comm hi₂] at hp
  simpa only [map_smul, smul_eq_mul, mul_comm] using hp

end HartreeF.EnergySpace
