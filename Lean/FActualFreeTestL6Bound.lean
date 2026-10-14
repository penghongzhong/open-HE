import FRetardedScalarL2
import FEnergyFreeConsumers

/-! The actual bilinear-transpose free test has the same even Fourier phase
as the constructed Schwartz free evolution. Sobolev and true gradient
unitarity then give a time-uniform L6 bound for genuine L1 source pairings. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory FourierTransform
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.FreeTestBounds
open FreeFlow Retarded EnergySpace SobolevStretch StationarySelfTest

theorem phase_neg (t : ℝ) (x : FreeFlow.V) : phase t (-x) = phase t x := by
  simp only [phase, norm_neg]

/-- Exact identity for the existing bilinear-distribution test operator.
There is no complex conjugation or change in the sign of physical time. -/
theorem freeTest_eq_freeSchwartz (t : ℝ) (φ : FreeFlow.Test) :
    freeTest t φ = freeSchwartz t φ := by
  let A : FreeFlow.Test := SchwartzMap.smulLeftCLM ℂ (phase t) (𝓕⁻ φ)
  let B : FreeFlow.Test := SchwartzMap.smulLeftCLM ℂ (phase t) (𝓕 φ)
  have hAB : (A : FreeFlow.V → ℂ) = fun x => B (-x) := by
    funext x
    change (SchwartzMap.smulLeftCLM ℂ (phase t) (𝓕⁻ φ)) x =
      (SchwartzMap.smulLeftCLM ℂ (phase t) (𝓕 φ)) (-x)
    rw [SchwartzMap.smulLeftCLM_apply_apply (phase_temperate t),
      SchwartzMap.smulLeftCLM_apply_apply (phase_temperate t), phase_neg]
    congr 1
  ext x
  change (𝓕 A) x = (𝓕⁻ B) x
  calc
    (𝓕 A) x = (𝓕 (A : FreeFlow.V → ℂ)) x := rfl
    _ = (𝓕 (fun y => B (-y))) x := congrArg (fun f : FreeFlow.V → ℂ => (𝓕 f) x) hAB
    _ = (𝓕⁻ (B : FreeFlow.V → ℂ)) x :=
      congrArg (fun f : FreeFlow.V → ℂ => f x) (Real.fourierInv_eq_fourier_comp_neg (B : FreeFlow.V → ℂ)).symm
    _ = (𝓕⁻ B) x :=
      congrArg (fun f : FreeFlow.V → ℂ => f x) (SchwartzMap.fourierInv_coe B).symm

/-- A genuine all-time L6 bound. Its constant depends on the fixed test's
homogeneous gradient norm and the existing ordinary Sobolev constant. -/
theorem freeTest_L6_norm_le (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (t : ℝ) (φ : FreeFlow.Test) :
    ‖(freeTest t φ).toLp 6 volume‖ ≤
      K ^ ((6 : ℝ)⁻¹) * pureGradientNorm (schwartzEnergyState φ) := by
  have h := energyValue_le_pureGradient hSob
    (freeEnergyState hDensity hSob t (schwartzEnergyState φ))
  rw [freeEnergyState_pureGradientNorm] at h
  simpa only [freeEnergyState_schwartz, schwartzEnergyState_value,
    freeTest_eq_freeSchwartz] using h

set_option pp.universes true
#check @phase_neg
#print axioms phase_neg
#check @freeTest_eq_freeSchwartz
#print axioms freeTest_eq_freeSchwartz
#check @freeTest_L6_norm_le
#print axioms freeTest_L6_norm_le
end HartreeF.FreeTestBounds
