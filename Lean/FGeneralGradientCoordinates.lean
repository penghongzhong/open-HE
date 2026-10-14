import FGeneralFrameNorms
import FCriticalAffineWeakGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing SobolevStretch CompactCross CriticalAffine AffineMixed EnergySpace

/-- The actual complex coordinate of the packed real/imaginary weak gradient. -/
def gradientCoordinate (j : Fin 3) (G : ℝ → Space → CGradient) : ℝ → Space → ℂ :=
  fun t x => G t x j

theorem gradientCoordinate_joint_stronglyMeasurable (j : Fin 3) (G : ℝ → Space → CGradient)
    (hG : StronglyMeasurable (fun z : ℝ × Space => G z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => gradientCoordinate j G z.1 z.2) :=
  (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp_stronglyMeasurable hG

theorem gradientCoordinate_continuous (j : Fin 3) (G : ℝ → Space → CGradient)
    (hG : Continuous (fun z : ℝ × Space => G z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradientCoordinate j G z.1 z.2) :=
  (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp hG

theorem gradientCoordinate_compact (j : Fin 3) (G : ℝ → Space → CGradient)
    (hG : HasCompactSupport (fun z : ℝ × Space => G z.1 z.2)) :
    HasCompactSupport (fun z : ℝ × Space => gradientCoordinate j G z.1 z.2) :=
  hG.comp_left (g := fun v : CGradient => v j) (by simp)

/-- Coordinate critical norm is bounded by the actual packed norm, not identified with it. -/
theorem gradientCoordinate_mixed_le {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hqTop : q ≠ ∞)
    (j : Fin 3) (G : ℝ → Space → CGradient)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (gradientCoordinate j G) ≤ mixedNorm volume volume p q G :=
  mixed_mono hq0 hqTop ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp_aestronglyMeasurable hG)
    (fun t x => PiLp.norm_apply_le (G t x) j)

theorem gradientCoordinate_error_mixed_le {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hqTop : q ≠ ∞)
    (j : Fin 3) (G H : ℝ → Space → CGradient)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (fun t x => gradientCoordinate j G t x - gradientCoordinate j H t x) ≤
      mixedNorm volume volume p q (fun t x => G t x - H t x) := by
  exact gradientCoordinate_mixed_le hq0 hqTop j (fun t x => G t x - H t x) (hG.sub hH)

/-- On canonical EnergyState fields this is exactly the real weak coordinate derivative. -/
theorem gradientCoordinate_state (g : ℝ → EnergyState) (j : Fin 3) :
    gradientCoordinate j (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) =
      (fun t => (energyGradient j (g t) : Space → ℂ)) := by
  funext t x
  exact state_complexGradient_coordinate (g t) x j

/-- Spatial weak coupling survives the literal physical frame with weights 1/2 and 3/2. -/
theorem seedFrame_inDotH1 {a : ℝ} (ha : 0 < a) (y : Space) (s : ℝ)
    {u : ℝ → Space → ℂ} {U V : ℝ → Space → Space}
    (hd : ∀ t, InDotH1 (u t) (U t) (V t)) (t : ℝ) :
    InDotH1 (seedFrame a y s (1/2) u t)
      (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) U t)
      (parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) V t) := by
  have hp : a⁻¹ * Real.sqrt a⁻¹ = (a⁻¹) ^ (3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      a⁻¹ * (a⁻¹) ^ (1/2 : ℝ) = (a⁻¹) ^ (1 : ℝ) * (a⁻¹) ^ (1/2 : ℝ) := by rw [Real.rpow_one]
      _ = (a⁻¹) ^ ((1 : ℝ) + 1/2) := (Real.rpow_add (inv_pos.mpr ha) _ _).symm
      _ = _ := by norm_num
  have hv : valuePullback a⁻¹ (-(a⁻¹ • y)) (u (timeAffine a⁻¹ s t)) =
      seedFrame a y s (1/2) u t := by
    funext x
    simp only [valuePullback, seedFrame, parabolicField, Real.sqrt_eq_rpow]
  have hgrad (G : ℝ → Space → Space) :
      gradientPullback a⁻¹ (-(a⁻¹ • y)) (G (timeAffine a⁻¹ s t)) =
      parabolicField a⁻¹ (-(a⁻¹ • y)) s (3/2) G t := by
    funext x
    simp only [gradientPullback, parabolicField, hp]
  rw [← hv, ← hgrad U, ← hgrad V]
  exact inDotH1_affine_pullback (hd (timeAffine a⁻¹ s t)) (inv_pos.mpr ha) (-(a⁻¹ • y))

#print axioms gradientCoordinate_error_mixed_le
#print axioms gradientCoordinate_state
#print axioms seedFrame_inDotH1
end HartreeF.GeneralProfileCross
