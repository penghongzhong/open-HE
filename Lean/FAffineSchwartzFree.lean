import FAffineFourierTransform
import FFreeFlowCore
import FEnergyFreeProperties
import FCriticalAffineIsometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory FourierTransform
open scoped RealInnerProductSpace SchwartzMap
namespace HartreeF.FreeAffine
open CriticalAffine EnergySpace
attribute [local irreducible] energySubmodule

theorem affine_antilipschitz {a : ℝ} (ha : 0<a) (b : Space) :
    AntilipschitzWith ⟨a⁻¹, inv_nonneg.mpr ha.le⟩ (affine a b) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  change ‖x-y‖≤a⁻¹*‖(a • x+b)-(a • y+b)‖
  rw [add_sub_add_right_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]

/-- Actual homogeneous affine action on Schwartz space. -/
def affineSchwartz {a : ℝ} (ha : 0<a) (b : Space) : Test →L[ℂ] Test :=
  Real.sqrt a • SchwartzMap.compCLMOfAntilipschitz ℂ
    (show (affine a b).HasTemperateGrowth by unfold affine; fun_prop)
    (affine_antilipschitz ha b)

theorem affineSchwartz_apply {a : ℝ} (ha : 0<a) (b : Space) (φ : Test) (x : Space) :
    affineSchwartz ha b φ x=valuePullback a b φ x := rfl

theorem affineSchwartz_fourier {a : ℝ} (ha : 0<a) (b : Space) (φ : Test) (ξ : Space) :
    𝓕 (affineSchwartz ha b φ) ξ=
      (Real.sqrt a*(a^3)⁻¹) •
        (Real.fourierChar (inner ℝ b (a⁻¹ • ξ)) • 𝓕 φ (a⁻¹ • ξ)) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  exact fourier_valuePullback ha b φ ξ

/-- Exact phase scaling, including the fixed (2*pi)^2 factor. -/
theorem free_phase_affine_scale {a : ℝ} (ha : 0<a) (t : ℝ) (ξ : Space) :
    FreeFlow.phase (a^2*t) (a⁻¹ • ξ)=FreeFlow.phase t ξ := by
  have hn : (a^2*t)*((2*Real.pi)^2*‖a⁻¹ • ξ‖^2)=t*((2*Real.pi)^2*‖ξ‖^2) := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    field_simp
  unfold FreeFlow.phase
  congr 1
  calc
    _ = -Complex.I*Complex.ofReal ((a^2*t)*((2*Real.pi)^2*‖a⁻¹ • ξ‖^2)) := by
      simp only [Complex.ofReal_mul]; ring
    _ = -Complex.I*Complex.ofReal (t*((2*Real.pi)^2*‖ξ‖^2)) := by rw [hn]
    _ = _ := by simp only [Complex.ofReal_mul]; ring

/-- Actual free/affine covariance on Schwartz functions, derived from the
literal Fourier formula rather than an additional analytic interface. -/
theorem freeSchwartz_affine {a : ℝ} (ha : 0<a) (b : Space) (t : ℝ) (φ : Test) :
    FreeFlow.freeSchwartz t (affineSchwartz ha b φ)=
      affineSchwartz ha b (FreeFlow.freeSchwartz (a^2*t) φ) := by
  have hf : 𝓕 (FreeFlow.freeSchwartz t (affineSchwartz ha b φ))=
      𝓕 (affineSchwartz ha b (FreeFlow.freeSchwartz (a^2*t) φ)) := by
    ext ξ
    rw [FreeFlow.freeSchwartz_fourier, affineSchwartz_fourier, affineSchwartz_fourier,
      FreeFlow.freeSchwartz_fourier, free_phase_affine_scale ha]
    simp only [Circle.smul_def, Complex.real_smul, smul_eq_mul]
    ring
  have h := congrArg (fun ψ : Test => 𝓕⁻ ψ) hf
  simpa only [fourierInv_fourier_eq] using h

/-- The Schwartz action realizes the already proved canonical weak-gradient
EnergyState action. No scalar L2 hypothesis is imposed on a general state. -/
theorem affineState_schwartz {a : ℝ} (ha : 0<a) (b : Space) (φ : Test) :
    affineState ha b (schwartzEnergyState φ)=schwartzEnergyState (affineSchwartz ha b φ) := by
  apply energyValue_injective
  apply Lp.ext
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae (schwartzEnergyState_value_ae φ)
  filter_upwards [affineState_value_ae ha b (schwartzEnergyState φ),
    schwartzEnergyState_value_ae (affineSchwartz ha b φ),hi] with x haff hsch hi
  rw [haff,hsch]
  change Real.sqrt a • energyValue (schwartzEnergyState φ) (affine a b x)=
    Real.sqrt a • φ (affine a b x)
  rw [hi]

#print axioms affine_antilipschitz
#print axioms affineSchwartz
#print axioms affineSchwartz_apply
#print axioms affineSchwartz_fourier
#print axioms free_phase_affine_scale
#print axioms freeSchwartz_affine
#print axioms affineState_schwartz
end HartreeF.FreeAffine
