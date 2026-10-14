import FLinearProfileFrame
import FWeakGradientEnergyDual

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.ProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest CriticalAffine
attribute [local irreducible] energySubmodule

/-- A genuinely varying weak test is controlled by the uniform sequence norm
and its strong test error; fixed-test weak convergence alone is not substituted. -/
theorem weak_inner_moving_test {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : ℕ → E} {f : E} {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B)
    (hw : ∀ v : E, Tendsto (fun n => inner ℝ (u n) v) atTop (𝓝 (inner ℝ f v)))
    {v : ℕ → E} {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => inner ℝ (u n) (v n)) atTop (𝓝 (inner ℝ f w)) := by
  have hd : Tendsto (fun n => ‖v n-w‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hv.sub_const w).norm
  have hz : Tendsto (fun n => inner ℝ (u n) (v n-w)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht := hd.const_mul B
    simp only [mul_zero] at ht
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => (norm_inner_le_norm (u n) (v n-w)).trans
        (mul_le_mul_of_nonneg_right (hB n) (norm_nonneg _))) ht
  have ht := hz.add (hw w)
  simpa only [inner_sub_right, sub_add_cancel, zero_add] using ht

theorem freeL2_real_adjoint (t : ℝ) (u v : L2) :
    inner ℝ (FreeFlow.freeL2 t u) v=inner ℝ u (FreeFlow.freeL2 (-t) v) := by
  let U : L2 →ₗᵢ[ℝ] L2 :=
    { (FreeFlow.freeL2 t).toLinearMap.restrictScalars ℝ with norm_map' := FreeFlow.freeL2_norm t }
  have h := U.inner_map_map u (FreeFlow.freeL2 (-t) v)
  change inner ℝ (FreeFlow.freeL2 t u) (FreeFlow.freeL2 t (FreeFlow.freeL2 (-t) v)) = _ at h
  rwa [FreeFlow.freeL2_inverse] at h

/-- Actual L2 weak transport at convergent, varying free times. -/
theorem freeL2_weak_moving_time {u : ℕ → L2} {f : L2} {B : ℝ}
    (hB : ∀ n, ‖u n‖ ≤ B)
    (hw : ∀ v : L2, Tendsto (fun n => inner ℝ (u n) v) atTop (𝓝 (inner ℝ f v)))
    {s : ℕ → ℝ} {t : ℝ} (hs : Tendsto s atTop (𝓝 t)) (v : L2) :
    Tendsto (fun n => inner ℝ (FreeFlow.freeL2 (s n) (u n)) v) atTop
      (𝓝 (inner ℝ (FreeFlow.freeL2 t f) v)) := by
  have htest := (FreeFlow.freeL2_time_continuous v).tendsto (-t) |>.comp hs.neg
  have ht := weak_inner_moving_test hB hw htest
  simpa only [Function.comp_def, ← freeL2_real_adjoint] using ht

/-- Coordinate-wise transport uses the actual free-gradient identity. -/
theorem freeEnergyState_gradient_weak_moving_time
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    {u : ℕ → EnergyState} {f : EnergyState} {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B)
    (hw : GradientWeakLimit u f) {s : ℕ → ℝ} {t : ℝ} (hs : Tendsto s atTop (𝓝 t)) :
    GradientWeakLimit (fun n => freeEnergyState hDensity hSob (s n) (u n))
      (freeEnergyState hDensity hSob t f) := by
  intro j v
  have hb (n : ℕ) : ‖energyGradient j (u n)‖ ≤ B :=
    (energyState_gradient_norm_le (u n) j).trans (hB n)
  simpa only [freeEnergyState_gradient] using freeL2_weak_moving_time hb (hw j) hs v

/-- A source-convention full-frame weak limit becomes a spatial-frame weak
limit only after the finite normalized time and moving-test argument are used. -/
theorem spatialPullback_weak_of_finite_fullFrame
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n) (y : ℕ → Space) (s : ℕ → ℝ)
    {u : ℕ → EnergyState} (phi : EnergyState) {B t : ℝ}
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hw : GradientWeakLimit
      (fun n => (linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n)).symm (u n)) phi)
    (hs : Tendsto s atTop (𝓝 t)) :
    GradientWeakLimit (fun n => (criticalAffineState (lambda n) (hlambda n) (y n)).symm (u n))
      (freeEnergyState hDensity hSob t phi) := by
  let A (n : ℕ) := linearProfileFrame hDensity hSob (lambda n) (hlambda n) (y n) (s n)
  let z (n : ℕ) := (A n).symm (u n)
  have hp (n : ℕ) : pureGradientNorm (z n)=pureGradientNorm (u n) := by
    have hh := linearProfileFrame_pureGradientNorm hDensity hSob (lambda n) (hlambda n) (y n) (s n) (z n)
    have hz : A n (z n)=u n := (A n).apply_symm_apply (u n)
    change pureGradientNorm (A n (z n))=pureGradientNorm (z n) at hh
    rw [hz] at hh
    exact hh.symm
  have hb (n : ℕ) : ‖z n‖ ≤ max (K^((6:ℝ)⁻¹)) 1*B := by
    exact (energyState_le_pureGradient hSob (z n)).trans
      (mul_le_mul_of_nonneg_left (by rw [hp]; exact hB n) (le_trans zero_le_one (le_max_right _ _)))
  have ht := freeEnergyState_gradient_weak_moving_time hDensity hSob hb hw hs
  have he (n : ℕ) : freeEnergyState hDensity hSob (s n) (z n)=
      (criticalAffineState (lambda n) (hlambda n) (y n)).symm (u n) := by
    exact freeEnergyState_inverse hDensity hSob (s n) _
  simpa only [he] using ht

#print axioms weak_inner_moving_test
#print axioms freeL2_real_adjoint
#print axioms freeL2_weak_moving_time
#print axioms freeEnergyState_gradient_weak_moving_time
#print axioms spatialPullback_weak_of_finite_fullFrame
end HartreeF.ProfileEnergy
