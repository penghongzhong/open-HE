import FActualFreeRemainderInputs
import FFreeLocalCompactness

/-! The local compactness theorem is consumed on the actual inverse-frame
remainder coordinates. No new local-strong or high-frequency hypothesis.
Static candidate, UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace HartreeF.FreeRemainderInputs
open EnergySpace SobolevStretch StationarySelfTest ProfileEnergy ActualStrichartz TimeHolder

/-- Genuine local mixed domains hold at every index without the weak-limit input. -/
theorem normalizedFreeGradient_local_finite (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (J j : ℕ) (k : Fin 3) (n : ℕ) (T R : ℝ) (z : V) :
    mixedNorm (volume.restrict (Set.Icc (-T) T)) (volume.restrict (Metric.ball z R)) 2 2
      (normalizedFreeGradient hDensity hSob P u J j k n) ≠ ∞ :=
  FreeLocalCompactness.freeJoint_cylinder_mixedNorm_finite _ T R z

/-- Actual original-sequence local strong convergence at fixed eligible J,j. -/
theorem normalizedFreeGradient_local_tendsto (hDensity : OrdinaryH1Density) {K B : ℝ}
    (hSob : OrdinarySobolev K) (q : Highpass.Cutoff)
    (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hp : LinearProfileProperties hDensity hSob u P)
    (J j : ℕ) (hj : j < J) (hJ : (J : WithTop ℕ) ≤ P.count)
    (k : Fin 3) {T R : ℝ} (hT : 0 < T) (hR : 0 < R) (z : V) :
    Tendsto (fun n => mixedNorm (volume.restrict (Set.Icc (-T) T))
      (volume.restrict (Metric.ball z R)) 2 2
      (normalizedFreeGradient hDensity hSob P u J j k n)) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (pureGradientNorm_nonneg (u 0)).trans (hB 0)
  exact FreeLocalCompactness.freeJoint_local_mixedNorm_tendsto_zero q
    (headGradientCap_nonneg hB0 P J)
    (fun n => inverseFrameRemainder_coordinate_bound hDensity hSob P u hB J j n k)
    (fun v => inverseFrameRemainder_weak_zero hDensity hSob P u hp J j hj hJ k v)
    hT hR z

end HartreeF.FreeRemainderInputs
