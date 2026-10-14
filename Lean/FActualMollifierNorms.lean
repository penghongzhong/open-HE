import FJointCutoffMollification
import FActualMollifierTransport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation CutoffApproximation SobolevStretch EnergySpace CriticalTimeSobolev

/-- Native S-convergence of the actual mollified cutoff values of an EnergyState profile.
The selected jointly measurable fields are used only inside the proof. -/
theorem actual_mollifiedCutoff_S_tendsto (g : ℝ → EnergyState)
    (hg : AEStronglyMeasurable g volume)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (n : ℕ) {φ : ℕ → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m => mixedNorm volume volume 10 10
      (fun t x => mollifiedCutoffValue n (φ m) g t x - spacetimeCutoff n (stateValueField g) t x))
      atTop (𝓝 0) := by
  let r := energyJointFields volume g hg
  have hSr : mixedNorm volume volume 10 10 r.u ≠ ∞ := by
    rwa [jointFields_value_mixedNorm g r]
  have h := cutoff_mollify_S_tendsto n hφ r.u r.joint_u hSr
  apply h.congr'
  filter_upwards [] with m
  exact (mollifiedCutoffValue_error_mixedNorm_eq_joint g r n (φ m) 10 10).symm

/-- Native W-convergence for the same mollified cutoff values and their actual packed weak gradients. -/
theorem actual_mollifiedCutoff_W_tendsto (g : ℝ → EnergyState)
    (hg : AEStronglyMeasurable g volume)
    (hS : mixedNorm volume volume 10 10 (stateValueField g) ≠ ∞)
    (hW : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (stateRealGradientField g t) (stateImagGradientField g t)) ≠ ∞)
    (n : ℕ) {φ : ℕ → ContDiffBump (0 : Space)}
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m => mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t x => mollifiedCutoffPackedGradient n (φ m) g t x - spacetimeCutoffGradient n
        (stateValueField g) (fun s => complexGradient (stateRealGradientField g s)
          (stateImagGradientField g s)) t x)) atTop (𝓝 0) := by
  let r := energyJointFields volume g hg
  have hSr : mixedNorm volume volume 10 10 r.u ≠ ∞ := by
    rwa [jointFields_value_mixedNorm g r]
  have hWr : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t => complexGradient (r.U t) (r.V t)) ≠ ∞ := by
    rwa [jointFields_packed_mixedNorm g r]
  have h := cutoff_mollify_W_tendsto n hφ r.u (fun t => complexGradient (r.U t) (r.V t))
    r.joint_u (packedGradient_joint_stronglyMeasurable r.joint_U r.joint_V) hSr hWr
  apply h.congr'
  filter_upwards [] with m
  exact (mollifiedCutoffPackedGradient_error_mixedNorm_eq_joint g r n (φ m) 10
    (ENNReal.ofReal (30/13 : ℝ))).symm

/-- Radius-independent homogeneous E bound for the actual mollified cutoff packed gradient.
This is the same explicit cutoff bound, preserved by genuine spatial convolution. -/
theorem actual_mollifiedCutoff_energy_le {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : AEStronglyMeasurable g volume) (n : ℕ)
    (φ : ContDiffBump (0 : Space)) :
    mixedNorm volume volume ∞ 2 (mollifiedCutoffPackedGradient n φ g) ≤
      (1 + (cutoffGradientBound : ℝ≥0∞) * ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹))) * curveEnergy g := by
  let r := energyJointFields volume g hg
  rw [mollifiedCutoffPackedGradient_mixedNorm_eq_joint g r n φ ∞ 2]
  exact (cutoff_mollify_energy_le n φ r.u r.U r.V r.joint_u r.joint_U r.joint_V r.inDotH1).trans
    (actual_profile_cutoff_energy hSob g hg n)

theorem actual_mollifiedCutoff_energy_ne_top {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : AEStronglyMeasurable g volume) (hE : curveEnergy g ≠ ∞)
    (n : ℕ) (φ : ContDiffBump (0 : Space)) :
    mixedNorm volume volume ∞ 2 (mollifiedCutoffPackedGradient n φ g) ≠ ∞ :=
  ne_top_of_le_ne_top (by finiteness) (actual_mollifiedCutoff_energy_le hSob g hg n φ)

#print axioms actual_mollifiedCutoff_S_tendsto
#print axioms actual_mollifiedCutoff_W_tendsto
#print axioms actual_mollifiedCutoff_energy_le
#print axioms actual_mollifiedCutoff_energy_ne_top
end HartreeF.ProfileSpatialSmoothing
