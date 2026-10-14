import FActualMollifierNorms

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation CutoffApproximation SobolevStretch EnergySpace CriticalTimeSobolev

/-- The actual canonical mollification has the same error against the selected joint cutoff. -/
theorem mollifiedCutoffValue_error_against_joint_eq (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) (n : ℕ) (φ : ContDiffBump (0 : Space)) (p q : ℝ≥0∞) :
    mixedNorm volume volume p q
      (fun t x => mollifiedCutoffValue n φ g t x - spacetimeCutoff n r.u t x) =
      mixedNorm volume volume p q (fun t x => spatialMollify φ (spacetimeCutoff n r.u t) x -
        spacetimeCutoff n r.u t x) := by
  apply eLpNorm_congr_ae
  filter_upwards [jointFields_cutoff_value_ae g r n] with t ht
  simp only [mollifiedCutoffValue, spatialMollify_congr φ ht]

/-- The actual canonical packed gradient has the same error against the selected joint cutoff gradient. -/
theorem mollifiedCutoffPackedGradient_error_against_joint_eq (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) (n : ℕ) (φ : ContDiffBump (0 : Space)) (p q : ℝ≥0∞) :
    mixedNorm volume volume p q
      (fun t x => mollifiedCutoffPackedGradient n φ g t x -
        spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t x) =
      mixedNorm volume volume p q (fun t x => spatialMollify φ
        (spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t) x -
        spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t x) := by
  apply eLpNorm_congr_ae
  filter_upwards [jointFields_cutoff_packed_ae g r n] with t ht
  simp only [mollifiedCutoffPackedGradient_eq_spatialMollify, spatialMollify_congr φ ht]

/-- The fixed-cutoff S limit in the form consumed by a common-scale diagonal triangle argument. -/
theorem actual_mollifiedCutoff_S_joint_tendsto (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (n : ℕ) {φ : ℕ → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m => mixedNorm volume volume 10 10
      (fun t x => mollifiedCutoffValue n (φ m) g t x - spacetimeCutoff n r.u t x))
      atTop (𝓝 0) := by
  have hSr : mixedNorm volume volume 10 10 r.u ≠ ∞ := by
    rwa [jointFields_value_mixedNorm g r]
  have h := cutoff_mollify_S_tendsto n hφ r.u r.joint_u hSr
  apply h.congr'
  filter_upwards [] with m
  exact (mollifiedCutoffValue_error_against_joint_eq g r n (φ m) 10 10).symm

/-- The fixed-cutoff W limit for the same actual packed weak gradient, relative to the joint cutoff. -/
theorem actual_mollifiedCutoff_W_joint_tendsto (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞)
    (n : ℕ) {φ : ℕ → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m => mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t x => mollifiedCutoffPackedGradient n (φ m) g t x -
        spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t x))
      atTop (𝓝 0) := by
  have hSr : mixedNorm volume volume 10 10 r.u ≠ ∞ := by
    rwa [jointFields_value_mixedNorm g r]
  have hWr : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (r.U t) (r.V t)) ≠ ∞ := by
    rwa [jointFields_packed_mixedNorm g r]
  have h := cutoff_mollify_W_tendsto n hφ r.u (fun t => complexGradient (r.U t) (r.V t))
    r.joint_u (packedGradient_joint_stronglyMeasurable r.joint_U r.joint_V) hSr hWr
  apply h.congr'
  filter_upwards [] with m
  exact (mollifiedCutoffPackedGradient_error_against_joint_eq g r n (φ m) 10
    (ENNReal.ofReal (30/13 : ℝ))).symm

#print axioms actual_mollifiedCutoff_S_joint_tendsto
#print axioms actual_mollifiedCutoff_W_joint_tendsto
end HartreeF.ProfileSpatialSmoothing
