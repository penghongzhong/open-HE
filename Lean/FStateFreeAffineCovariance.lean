import FAffineSchwartzFree
import FLinearProfileFrame

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace HartreeF.FreeAffine
open CriticalAffine EnergySpace SobolevStretch StationarySelfTest ProfileEnergy
attribute [local irreducible] energySubmodule

/-- Extend the actual Schwartz covariance through the homogeneous graph-space
density and the two genuine bounded linear maps. -/
theorem freeEnergyState_affine (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {a : ℝ} (ha : 0<a) (b : Space) (t : ℝ) (u : EnergyState) :
    freeEnergyState hDensity hSob t (affineState ha b u)=
      affineState ha b (freeEnergyState hDensity hSob (a^2*t) u) := by
  obtain ⟨φ,hφ⟩ := schwartzEnergyState_approximation hDensity hSob u
  have he (n : ℕ) : freeEnergyState hDensity hSob t (affineState ha b (schwartzEnergyState (φ n)))=
      affineState ha b (freeEnergyState hDensity hSob (a^2*t) (schwartzEnergyState (φ n))) := by
    rw [affineState_schwartz, freeEnergyState_schwartz, freeEnergyState_schwartz,
      affineState_schwartz, freeSchwartz_affine]
  have hl := ((freeEnergyCLM hDensity hSob t).continuous.comp
    (affineStateEquiv ha b).continuous).tendsto u |>.comp hφ
  have hr := ((affineStateEquiv ha b).continuous.comp
    (freeEnergyCLM hDensity hSob (a^2*t)).continuous).tendsto u |>.comp hφ
  change Tendsto (fun n => freeEnergyState hDensity hSob t
    (affineState ha b (schwartzEnergyState (φ n)))) atTop
    (𝓝 (freeEnergyState hDensity hSob t (affineState ha b u))) at hl
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

/-- The literal positive length-scale convention: U(t) T(lambda,y) equals
T(lambda,y) U(t/lambda^2) on every actual EnergyState. -/
theorem freeEnergyState_criticalAffine (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (lambda : ℝ) (hlambda : 0<lambda)
    (y : Space) (t : ℝ) (u : EnergyState) :
    freeEnergyState hDensity hSob t (criticalAffineState lambda hlambda y u)=
      criticalAffineState lambda hlambda y (freeEnergyState hDensity hSob (t/lambda^2) u) := by
  have ht : (lambda⁻¹)^2*t=t/lambda^2 := by rw [inv_pow, div_eq_mul_inv, mul_comm]
  change freeEnergyState hDensity hSob t
    (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) u)=
    affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y))
      (freeEnergyState hDensity hSob (t/lambda^2) u)
  rw [← ht]
  exact freeEnergyState_affine hDensity hSob (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) t u

/-- Exact evolution of a source-order linear profile frame, with its normalized
time retained. This is linear trajectory algebra, not nonlinear reconstruction. -/
theorem linearProfileFrame_free_evolution (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (lambda : ℝ) (hlambda : 0<lambda)
    (y : Space) (s t : ℝ) (phi : EnergyState) :
    freeEnergyState hDensity hSob t (linearProfileFrame hDensity hSob lambda hlambda y s phi)=
      linearProfileFrame hDensity hSob lambda hlambda y (s+t/lambda^2) phi := by
  rw [linearProfileFrame_apply, freeEnergyState_criticalAffine,
    ← freeEnergyState_add_time, linearProfileFrame_apply, add_comm (t/lambda^2) s]

/-- The source physical time center is exactly -lambda^2*s. -/
theorem linearProfileFrame_physical_time_center (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (lambda : ℝ) (hlambda : 0<lambda)
    (y : Space) (s t : ℝ) (phi : EnergyState) :
    freeEnergyState hDensity hSob t (linearProfileFrame hDensity hSob lambda hlambda y s phi)=
      criticalAffineState lambda hlambda y
        (freeEnergyState hDensity hSob ((t-(-(lambda^2*s)))/lambda^2) phi) := by
  rw [linearProfileFrame_free_evolution, linearProfileFrame_apply]
  have ht : s+t/lambda^2=(t-(-(lambda^2*s)))/lambda^2 := by
    field_simp
    ring
  rw [ht]

#print axioms freeEnergyState_affine
#print axioms freeEnergyState_criticalAffine
#print axioms linearProfileFrame_free_evolution
#print axioms linearProfileFrame_physical_time_center
end HartreeF.FreeAffine
