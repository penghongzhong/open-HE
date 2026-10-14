import FProfileCutoffGradient
import FEnergyCriticalTimeConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ProfileApproximation
open TimeHolder CutoffApproximation SobolevStretch EnergySpace CriticalTimeSobolev

/-- Packing the two real gradients is a continuous, actual complex-vector operation. -/
theorem packedGradient_formula (U V : Space → Space) (x : Space) :
    complexGradient U V x = realEmbed (U x) + Complex.I • realEmbed (V x) := by
  ext j
  simp [complexGradient, realEmbed]

theorem packedGradient_joint_measurable {U V : ℝ → Space → Space}
    (hU : AEStronglyMeasurable (fun z : ℝ × Space => U z.1 z.2) (volume.prod volume))
    (hV : AEStronglyMeasurable (fun z : ℝ × Space => V z.1 z.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => complexGradient (U z.1) (V z.1) z.2)
      (volume.prod volume) := by
  simp_rw [packedGradient_formula]
  exact (realEmbed_continuous.comp_aestronglyMeasurable hU).add
    ((realEmbed_continuous.comp_aestronglyMeasurable hV).const_smul Complex.I)

theorem packedGradient_memLp {p : ℝ≥0∞} {U V : Space → Space}
    (hU : MemLp U p volume) (hV : MemLp V p volume) :
    MemLp (complexGradient U V) p volume := by
  have he (f : Space → Space) (hf : MemLp f p volume) :
      MemLp (fun x => realEmbed (f x)) p volume :=
    hf.of_le (realEmbed_continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (ae_of_all _ fun _ => (realEmbed_norm _).le)
  rw [show complexGradient U V = (fun x => realEmbed (U x)) +
    Complex.I • (fun x => realEmbed (V x)) from funext (packedGradient_formula U V)]
  exact (he U hU).add ((he V hV).const_smul Complex.I)

/-- The actual packed gradient L2 norm equals the pure-gradient norm of EnergyState. -/
theorem state_packedGradient_eLpNorm (z : EnergyState) :
    eLpNorm (complexGradient (energyProjectedGradient Complex.reCLM z)
      (energyProjectedGradient Complex.imCLM z)) 2 volume =
      ENNReal.ofReal (pureGradientNorm z) := by
  have hm := packedGradient_memLp (energyProjectedGradient_memLp Complex.reCLM z)
    (energyProjectedGradient_memLp Complex.imCLM z)
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  change ENNReal.ofReal ((kinetic (energyProjectedGradient Complex.reCLM z)
    (energyProjectedGradient Complex.imCLM z)) ^ ((2 : ℝ)⁻¹)) = _
  rw [state_kinetic_eq_gradientSquared]
  simp only [pureGradientNorm, Real.sqrt_eq_rpow, one_div]

/-- Extended homogeneous energy norm; no scalar L2 term is included. -/
def curveEnergy (g : ℝ → EnergyState) : ℝ≥0∞ :=
  eLpNorm (fun t => pureGradientNorm (g t)) ∞ volume

/-- The joint representatives retain the genuine packed gradient energy exactly. -/
theorem jointFields_energy_eq (g : ℝ → EnergyState) (r : EnergyJointFields volume g)
    (hg : AEStronglyMeasurable g volume) :
    mixedNorm volume volume ∞ 2 (fun t => complexGradient (r.U t) (r.V t)) = curveEnergy g := by
  have hpure : Continuous pureGradientNorm := by
    unfold pureGradientNorm gradientSquared
    fun_prop
  have hpn := hpure.comp_aestronglyMeasurable hg
  have hm := spatial_lp_time_measurable volume volume 2 (by norm_num) (by norm_num)
    (fun t => complexGradient (r.U t) (r.V t))
    (packedGradient_joint_measurable r.joint_U.aestronglyMeasurable r.joint_V.aestronglyMeasurable)
  apply eLpNorm_congr_enorm_ae hm hpn
  filter_upwards [r.slice_eq] with t ht
  have he : complexGradient (r.U t) (r.V t) =ᵐ[volume]
      complexGradient (energyProjectedGradient Complex.reCLM (g t))
        (energyProjectedGradient Complex.imCLM (g t)) := by
    filter_upwards [ht.2.1, ht.2.2] with x hU hV
    simp only [complexGradient, hU, hV]
  rw [enorm_eq_self, eLpNorm_congr_ae he, state_packedGradient_eLpNorm,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg (pureGradientNorm_nonneg _)]

/-- Sobolev's pointwise EnergyState estimate lifted to the actual global V norm. -/
theorem jointFields_value_sobolev_bound {K : ℝ} (hSob : OrdinarySobolev K)
    (g : ℝ → EnergyState) (r : EnergyJointFields volume g) :
    mixedNorm volume volume ∞ 6 r.u ≤ ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹)) * curveEnergy g := by
  let C : ℝ≥0 := ⟨K ^ ((6 : ℝ)⁻¹), Real.rpow_nonneg hSob.nonneg _⟩
  have hC : (C : ℝ≥0∞) = ENNReal.ofReal (K ^ ((6 : ℝ)⁻¹)) := by
    exact (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞)).symm
  rw [← hC]
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (spatial_lp_time_measurable volume volume 6 (by norm_num) (by norm_num) _
      r.joint_u.aestronglyMeasurable)
  filter_upwards [r.slice_eq] with t ht
  rw [enorm_eq_self, eLpNorm_congr_ae ht.1, ← Lp.enorm_def, ← ofReal_norm,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg (pureGradientNorm_nonneg _), hC,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hSob.nonneg _)]
  exact ENNReal.ofReal_le_ofReal (energyValue_le_pureGradient hSob (g t))

/-- All spatial cutoffs are contractions on the field norm. -/
theorem spatial_cutoff_mixed_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {p q : ℝ≥0∞} (hq0 : q ≠ 0) (hqTop : q ≠ ∞) (n : ℕ)
    (f : ℝ → Space → E)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume p q (fun t x => cutoff n x • f t x) ≤
      mixedNorm volume volume p q f := by
  apply mixed_mono hq0 hqTop
    (((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hf)
  intro t x
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg n x)]
  exact (mul_le_mul_of_nonneg_right (cutoff_le_one n x) (norm_nonneg _)).trans_eq (one_mul _)

/-- Uniform homogeneous cutoff energy bound from L3 times L6. -/
theorem spatial_cutoff_energy_bound (n : ℕ) (u : ℝ → Space → ℂ)
    (G : ℝ → Space → CGradient)
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume)) :
    mixedNorm volume volume ∞ 2 (spatialCutoffGradient n u G) ≤
      mixedNorm volume volume ∞ 2 G +
        (cutoffGradientBound : ℝ≥0∞) * mixedNorm volume volume ∞ 6 u := by
  let : ENNReal.HolderTriple 6 3 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    rw [ENNReal.toReal_add (by simp) (by simp)]
    norm_num⟩
  have hc : mixedNorm volume volume ∞ 2 (cutoffCorrection n u) ≤
      (cutoffGradientBound : ℝ≥0∞) * mixedNorm volume volume ∞ 6 u := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
      (spatial_lp_time_measurable volume volume 2 (by norm_num) (by norm_num) _
        (correction_joint_measurable n hu))
    filter_upwards [] with t
    exact (correction_slice_bound (p := 6) (by norm_num) n u t).trans
      (mul_le_mul' le_rfl (eLpNorm_indicator_le _
        (isOpen_lt continuous_const continuous_norm).measurableSet.nullMeasurableSet))
  exact (mixed_add_le (by simp) (by norm_num) (by norm_num) _ _
    (((cutoff_smooth n).continuous.comp continuous_snd).aestronglyMeasurable.smul hG)
    (correction_joint_measurable n hu)).trans
      (add_le_add (spatial_cutoff_mixed_le (by norm_num) (by norm_num) n G hG) hc)

#print axioms state_packedGradient_eLpNorm
#print axioms jointFields_energy_eq
#print axioms jointFields_value_sobolev_bound
#print axioms spatial_cutoff_energy_bound
end HartreeF.ProfileApproximation
