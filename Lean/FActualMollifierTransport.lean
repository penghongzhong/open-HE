import FActualMollifiedFields
import FSpatialSobolevCoupling

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology Convolution
namespace HartreeF.ProfileSpatialSmoothing
open TimeHolder ProfileApproximation CutoffApproximation SobolevStretch EnergySpace CriticalTimeSobolev

/-- Exact convolution identity for the actual packed gradient of the cutoff energy-state curve. -/
theorem mollifiedCutoffPackedGradient_eq_spatialMollify (n : ℕ)
    (φ : ContDiffBump (0 : Space)) (g : ℝ → EnergyState) (t : ℝ) :
    mollifiedCutoffPackedGradient n φ g t =
      spatialMollify φ (spacetimeCutoffGradient n (stateValueField g)
        (fun s => complexGradient (stateRealGradientField g s) (stateImagGradientField g s)) t) := by
  have hd := inDotH1_real_smul (cutoff_L2_and_dotH1 (energyState_inDotH1 (g t)) n).2
    (timeCutoff n t)
  have he := spatialMollify_complexGradient φ hd.real_weak.gradient_local hd.imag_weak.gradient_local
  change mollifiedCutoffPackedGradient n φ g t = _ at he
  rw [he]
  congr 1
  exact funext fun x => (spacetimeCutoffGradient_is_packed n (stateValueField g)
    (stateRealGradientField g) (stateImagGradientField g) t x).symm

/-- Equality of selected and canonical value representatives survives the exact cutoff. -/
theorem jointFields_cutoff_value_ae (g : ℝ → EnergyState) (r : EnergyJointFields volume g) (n : ℕ) :
    ∀ᵐ t ∂volume, spacetimeCutoff n r.u t =ᵐ[volume] spacetimeCutoff n (stateValueField g) t := by
  filter_upwards [r.slice_eq] with t ht
  filter_upwards [ht.1] with x hx
  simp only [spacetimeCutoff, stateValueField, hx]

/-- Equality of selected and canonical gradients survives the actual product-rule cutoff. -/
theorem jointFields_cutoff_packed_ae (g : ℝ → EnergyState) (r : EnergyJointFields volume g) (n : ℕ) :
    ∀ᵐ t ∂volume,
      spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t =ᵐ[volume]
      spacetimeCutoffGradient n (stateValueField g)
        (fun s => complexGradient (stateRealGradientField g s) (stateImagGradientField g s)) t := by
  filter_upwards [r.slice_eq] with t ht
  filter_upwards [ht.1, ht.2.1, ht.2.2] with x hx hU hV
  simp only [spacetimeCutoffGradient, spatialCutoffGradient, cutoffCorrection,
    complexGradient, stateValueField, stateRealGradientField, stateImagGradientField, hx, hU, hV]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial a.e. representative changes preserve every mollification error mixed norm. -/
theorem mixedNorm_spatialMollify_sub_congr (p q : ℝ≥0∞) (φ : ContDiffBump (0 : Space))
    {f g : ℝ → Space → E} (hfg : ∀ᵐ t ∂volume, f t =ᵐ[volume] g t) :
    mixedNorm volume volume p q (fun t x => spatialMollify φ (f t) x - f t x) =
      mixedNorm volume volume p q (fun t x => spatialMollify φ (g t) x - g t x) := by
  apply eLpNorm_congr_ae
  filter_upwards [hfg] with t ht
  apply eLpNorm_congr_ae
  have hm := spatialMollify_congr φ ht
  filter_upwards [ht] with x hx
  rw [hm, hx]

/-- The actual mollified packed-gradient norm is independent of the chosen joint representative. -/
theorem mollifiedCutoffPackedGradient_mixedNorm_eq_joint (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) (n : ℕ) (φ : ContDiffBump (0 : Space)) (p q : ℝ≥0∞) :
    mixedNorm volume volume p q (mollifiedCutoffPackedGradient n φ g) =
      mixedNorm volume volume p q (fun t => spatialMollify φ
        (spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t)) := by
  apply eLpNorm_congr_ae
  filter_upwards [jointFields_cutoff_packed_ae g r n] with t ht
  rw [mollifiedCutoffPackedGradient_eq_spatialMollify, spatialMollify_congr φ ht]

/-- Exact S-error norm transport from canonical state representatives to joint representatives. -/
theorem mollifiedCutoffValue_error_mixedNorm_eq_joint (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) (n : ℕ) (φ : ContDiffBump (0 : Space)) (p q : ℝ≥0∞) :
    mixedNorm volume volume p q
      (fun t x => mollifiedCutoffValue n φ g t x - spacetimeCutoff n (stateValueField g) t x) =
      mixedNorm volume volume p q (fun t x => spatialMollify φ (spacetimeCutoff n r.u t) x -
        spacetimeCutoff n r.u t x) :=
  (mixedNorm_spatialMollify_sub_congr p q φ (jointFields_cutoff_value_ae g r n)).symm

/-- Exact W-error norm transport, using the produced literal packed-gradient convolution identity. -/
theorem mollifiedCutoffPackedGradient_error_mixedNorm_eq_joint (g : ℝ → EnergyState)
    (r : EnergyJointFields volume g) (n : ℕ) (φ : ContDiffBump (0 : Space)) (p q : ℝ≥0∞) :
    mixedNorm volume volume p q
      (fun t x => mollifiedCutoffPackedGradient n φ g t x - spacetimeCutoffGradient n (stateValueField g)
        (fun s => complexGradient (stateRealGradientField g s) (stateImagGradientField g s)) t x) =
      mixedNorm volume volume p q (fun t x => spatialMollify φ
        (spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t) x -
        spacetimeCutoffGradient n r.u (fun s => complexGradient (r.U s) (r.V s)) t x) := by
  simp_rw [mollifiedCutoffPackedGradient_eq_spatialMollify]
  exact (mixedNorm_spatialMollify_sub_congr p q φ (jointFields_cutoff_packed_ae g r n)).symm

#print axioms mollifiedCutoffPackedGradient_eq_spatialMollify
#print axioms mollifiedCutoffPackedGradient_mixedNorm_eq_joint
#print axioms mollifiedCutoffValue_error_mixedNorm_eq_joint
#print axioms mollifiedCutoffPackedGradient_error_mixedNorm_eq_joint
end HartreeF.ProfileSpatialSmoothing
