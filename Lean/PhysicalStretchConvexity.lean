import PhysicalSpectralRepresentation

/-!
Actual physical stretch convexity is produced first for L1 densities from the
proved Phi representation and C1's native scalar convexity. The three-point
inequality is then passed through the actual C4/C5 compact-density cutoffs.
The general density never receives an assumed classical Fourier transform.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace HartreeF.PhysicalSpectral
open PhysicalStretch PhysicalDensity HeatRiesz GaussianFourierBridge BWork.Gaussian

theorem spectralStretchPair_convex {α : ℝ} (hα : 0 < α)
    {ω : Space} (hω : ‖ω‖ = 1) (b : Space → ℝ) {ξ : Space} (hξ : ξ ≠ 0) :
    ConvexOn ℝ (Ioi 0) (fun s => spectralStretchPair α ω b s ξ) := by
  have hsum : 0 < longitudinalSq ω ξ + transverseSq ω ξ := by
    rw [directional_square_decomposition]
    exact sq_pos_of_pos (norm_pos_iff.mpr hξ)
  have hc := convexOn_stretchKernel (show 0 ≤ α/2 by linarith)
    (longitudinalSq_nonneg ω ξ) (transverseSq_nonneg hω ξ) hsum
  have hm := ConvexOn.smul (sq_nonneg ‖paperFourier b ξ‖) hc
  apply hm.congr
  intro s _
  change ‖paperFourier b ξ‖^2 * stretchKernel (α/2) (longitudinalSq ω ξ) (transverseSq ω ξ) s = _
  unfold spectralStretchPair
  ring

/-- Three finite actual spectral integrals integrate the native pointwise Phi convexity. -/
theorem physicalStretch_convex_L1 {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {ω : Space} (hω : ‖ω‖ = 1) {b : Space → ℝ} (hb : Integrable b volume)
    (hb0 : ∀ x, 0 ≤ b x) (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    ConvexOn ℝ (Ioi 0) (physicalStretchEnergy α (standardRieszConstant α) ω b) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro u hu v hv p q hp hq hpq
  have hz : 0 < p*u+q*v := by
    have h := (convex_Ioi (0:ℝ)) hu hv hp hq hpq
    simpa only [smul_eq_mul, Set.mem_Ioi] using h
  have hU := physicalStretch_spectral_domain_and_identity hα hα3 hω hu hb hb0 hpair
  have hV := physicalStretch_spectral_domain_and_identity hα hα3 hω hv hb hb0 hpair
  have hZ := physicalStretch_spectral_domain_and_identity hα hα3 hω hz hb hb0 hpair
  have hi : (∫ ξ, spectralStretchPair α ω b (p*u+q*v) ξ) ≤
      p*(∫ ξ, spectralStretchPair α ω b u ξ) + q*(∫ ξ, spectralStretchPair α ω b v ξ) := by
    calc
      _ ≤ ∫ ξ, p*spectralStretchPair α ω b u ξ + q*spectralStretchPair α ω b v ξ := by
        apply integral_mono_ae hZ.1 ((hU.1.const_mul p).add (hV.1.const_mul q))
        filter_upwards [frequency_ne_zero_ae] with ξ hξ
        have h := (spectralStretchPair_convex hα hω b hξ).2 hu hv hp hq hpq
        simpa only [smul_eq_mul, Pi.add_apply] using h
      _ = _ := by
        rw [integral_add (hU.1.const_mul p) (hV.1.const_mul q), integral_const_mul, integral_const_mul]
  change physicalStretchEnergy α (standardRieszConstant α) ω b (p*u+q*v) ≤
    p*physicalStretchEnergy α (standardRieszConstant α) ω b u +
    q*physicalStretchEnergy α (standardRieszConstant α) ω b v
  rw [hZ.2, hU.2, hV.2]
  exact (mul_le_mul_of_nonneg_left hi paperInverseFactor_pos.le).trans_eq (by ring)

/-- The actual original-pair domain is inherited by each compact density cutoff. -/
theorem standardRiesz_truncated_pair_integrable {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {b : Space → ℝ} (hb : AEStronglyMeasurable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) (n : ℕ) :
    Integrable (standardRieszPair α (truncate b n)) (volume.prod volume) := by
  apply truncated_pair_integrable
  · exact (measurable_const.mul
      (((continuous_fst.sub continuous_snd).norm.measurable).pow_const (α-3))).aestronglyMeasurable
  · intro q
    unfold rieszKernel
    exact mul_nonneg (standardRieszConstant_pos hα hα3).le (Real.rpow_nonneg (norm_nonneg _) _)
  · exact hb
  · exact hb0
  · exact hpair

/-- Genuine physical convexity for arbitrary nonnegative finite-energy densities.
Only the compact L1 cutoffs have Fourier transforms used in the proof. -/
theorem physicalStretch_convex {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {ω : Space} (hω : ‖ω‖ = 1) {b : Space → ℝ} (hb : AEStronglyMeasurable b volume)
    (hb0 : ∀ x, 0 ≤ b x) (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    ConvexOn ℝ (Ioi 0) (physicalStretchEnergy α (standardRieszConstant α) ω b) := by
  have hn (n : ℕ) : ConvexOn ℝ (Ioi 0)
      (physicalStretchEnergy α (standardRieszConstant α) ω (truncate b n)) :=
    physicalStretch_convex_L1 hα hα3 hω (truncate_integrable hb hb0 n)
      (truncate_nonneg hb0 n) (standardRiesz_truncated_pair_integrable hα hα3 hb hb0 hpair n)
  have hlim (s : ℝ) (hs : 0 < s) :
      Tendsto (fun n : ℕ => physicalStretchEnergy α (standardRieszConstant α) ω (truncate b n) s)
        atTop (𝓝 (physicalStretchEnergy α (standardRieszConstant α) ω b s)) :=
    physicalStretch_truncation_tendsto hα3 (standardRieszConstant_pos hα hα3).le hω hs hb hb0 hpair
  refine ⟨convex_Ioi 0, ?_⟩
  intro u hu v hv p q hp hq hpq
  have hz : 0 < p*u+q*v := by
    have h := (convex_Ioi (0:ℝ)) hu hv hp hq hpq
    simpa only [smul_eq_mul, Set.mem_Ioi] using h
  change physicalStretchEnergy α (standardRieszConstant α) ω b (p*u+q*v) ≤
    p*physicalStretchEnergy α (standardRieszConstant α) ω b u +
    q*physicalStretchEnergy α (standardRieszConstant α) ω b v
  apply le_of_tendsto_of_tendsto (hlim _ hz)
    (((hlim u hu).const_mul p).add ((hlim v hv).const_mul q))
  exact Eventually.of_forall (fun n => by
    simpa only [smul_eq_mul] using (hn n).2 hu hv hp hq hpq)

#print axioms spectralStretchPair_convex
#print axioms physicalStretch_convex_L1
#print axioms standardRiesz_truncated_pair_integrable
#print axioms physicalStretch_convex
end HartreeF.PhysicalSpectral
