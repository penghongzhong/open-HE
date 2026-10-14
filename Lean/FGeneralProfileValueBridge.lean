import FActualProfileCompactApproximation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing EnergySpace SobolevStretch
attribute [local irreducible] energySubmodule
attribute [local instance 101] secondCountableTopologyEither_of_left

/-- The existing Sobolev inequality applied to the actual coupled weak-gradient fields. -/
theorem inDotH1_value_eLpNorm_le_packed {K : ℝ} (hSob : OrdinarySobolev K)
    {u : Space → ℂ} {U V : Space → Space} (h : InDotH1 u U V) :
    eLpNorm u 6 volume ≤ ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹)) *
      eLpNorm (complexGradient U V) 2 volume := by
  let z := inDotEnergyState h
  have hp : complexGradient (energyProjectedGradient Complex.reCLM z)
      (energyProjectedGradient Complex.imCLM z) =ᵐ[volume] complexGradient U V := by
    filter_upwards [inDotEnergyState_real_gradient_ae h, inDotEnergyState_imag_gradient_ae h] with x hx hy
    change energyProjectedGradient Complex.reCLM z x = U x at hx
    change energyProjectedGradient Complex.imCLM z x = V x at hy
    simp only [complexGradient, hx, hy]
  calc
    eLpNorm u 6 volume = ENNReal.ofReal ‖energyValue z‖ := by
      rw [← eLpNorm_congr_ae (inDotEnergyState_value_ae h), ← Lp.enorm_def, ← ofReal_norm]
    _ ≤ ENNReal.ofReal ((K ^ ((6 : ℝ)⁻¹)) * pureGradientNorm z) :=
      ENNReal.ofReal_le_ofReal (energyValue_le_pureGradient hSob z)
    _ = ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹)) * eLpNorm (complexGradient U V) 2 volume := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hSob.nonneg _),
        ← state_packedGradient_eLpNorm z, eLpNorm_congr_ae hp]

/-- Uniform V is produced from the coupled homogeneous E bound, with no small E-error assumption. -/
theorem coupled_value_mixed_le {K : ℝ} (hSob : OrdinarySobolev K)
    (u : ℝ → Space → ℂ) (U V : ℝ → Space → Space)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hd : ∀ᵐ t ∂volume, InDotH1 (u t) (U t) (V t)) :
    mixedNorm volume volume ∞ 6 u ≤ ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹)) *
      mixedNorm volume volume ∞ 2 (fun t => complexGradient (U t) (V t)) := by
  let C : ℝ≥0 := ⟨K ^ ((6 : ℝ)⁻¹), Real.rpow_nonneg hSob.nonneg _⟩
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹)) :=
    (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞)).symm
  rw [← hC]
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (spatial_lp_time_measurable volume volume 6 (by norm_num) (by norm_num) u hu)
  filter_upwards [hd] with t ht
  simpa only [enorm_eq_self, hC] using inDotH1_value_eLpNorm_le_packed hSob ht

/-- A radius-independent V bound for every actual coupled compact approximant. -/
theorem mollifiedCutoff_V_bound {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (hg : Continuous g) (n : ℕ) (φ : ContDiffBump (0 : Space)) :
    mixedNorm volume volume ∞ 6 (mollifiedCutoffValue n φ g) ≤
      ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹)) *
        ((1 + (cutoffGradientBound : ℝ≥0∞) * ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹))) * curveEnergy g) := by
  have hv := coupled_value_mixed_le hSob (mollifiedCutoffValue n φ g)
    (mollifiedCutoffRealGradient n φ g) (mollifiedCutoffImagGradient n φ g)
    (mollifiedCutoffValue_continuous n φ g hg).aestronglyMeasurable
    (ae_of_all _ (actual_mollifiedCutoff_inDotH1 n φ g))
  exact hv.trans (mul_le_mul' le_rfl (actual_mollifiedCutoff_energy_le hSob g hg.aestronglyMeasurable n φ))

#print axioms inDotH1_value_eLpNorm_le_packed
#print axioms coupled_value_mixed_le
#print axioms mollifiedCutoff_V_bound
end HartreeF.GeneralProfileCross
