import SpectralHeatTonelli

/-!
The actual finite standard-Riesz/Fourier energy bridge for nonnegative real L1
densities. The ONLY energy-domain input is absolute integrability of the original
physical Riesz pair. Both heat-time product domains and the weighted spectral
L1 domain are produced before Fubini. No target energy identity, weighted HLS,
Fourier convexity, or oscillatory time-space exchange is assumed.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace HartreeF.HeatRiesz
open GaussianFourierBridge PhysicalDensity ForcingDomain PressureDomain BWork.Gaussian

/-- The weighted spectral domain is a consequence of the finite physical energy. -/
theorem standardRiesz_L1_spectral_integrable {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {b : Space → ℝ} (hb : Integrable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    Integrable (fun ξ : Space => ‖ξ‖^(-α) * ‖paperFourier b ξ‖^2) volume :=
  weightedFourierEnergy_integrable_of_heatEnergy hα hb
    (physicalHeatEnergy_integrable hα hα3 hb.aestronglyMeasurable hb0 hpair)

/-- Exact actual Riesz/Fourier identity in the paper exp(-i xi dot x) convention. -/
theorem standardRiesz_L1_fourier {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {b : Space → ℝ} (hb : Integrable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    (∫ q, standardRieszPair α b q ∂volume.prod volume) =
      paperInverseFactor * ∫ ξ : Space, ‖ξ‖^(-α) * ‖paperFourier b ξ‖^2 := by
  have ht := physicalHeatEnergy_integrable hα hα3 hb.aestronglyMeasurable hb0 hpair
  exact (physicalRieszEnergy_eq_heatTime hα hα3 hb.aestronglyMeasurable hb0 hpair).trans
    (weightedFourierEnergy_eq_heatEnergy hα hb ht).symm

/-- A combined finite-domain certificate and identity, with no spectral input premise. -/
theorem standardRiesz_L1_domain_and_fourier {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {b : Space → ℝ} (hb : Integrable b volume) (hb0 : ∀ x, 0 ≤ b x)
    (hpair : Integrable (standardRieszPair α b) (volume.prod volume)) :
    Integrable (fun ξ : Space => ‖ξ‖^(-α) * ‖paperFourier b ξ‖^2) volume ∧
    (∫ q, standardRieszPair α b q ∂volume.prod volume) =
      paperInverseFactor * ∫ ξ : Space, ‖ξ‖^(-α) * ‖paperFourier b ξ‖^2 :=
  ⟨standardRiesz_L1_spectral_integrable hα hα3 hb hb0 hpair,
    standardRiesz_L1_fourier hα hα3 hb hb0 hpair⟩

/-- HLS supplies the physical pair for an L6 Hartree field with additionally L1 density.
The L1 density assumption is explicit and is not claimed for general homogeneous data. -/
theorem hartree_L1_density_domain_and_fourier {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) {f : Space → ℂ}
    (hf : MemLp f 6 volume) (hb : Integrable (powerDensity α f) volume) :
    Integrable (fun ξ : Space => ‖ξ‖^(-α) * ‖paperFourier (powerDensity α f) ξ‖^2) volume ∧
    (∫ x, potential α (standardRieszConstant α) f x * powerDensity α f x) =
      paperInverseFactor * ∫ ξ : Space, ‖ξ‖^(-α) * ‖paperFourier (powerDensity α f) ξ‖^2 := by
  have hp : Integrable (standardRieszPair α (powerDensity α f)) (volume.prod volume) :=
    rieszPairDensity_integrable hHLS hf
  have h0 : ∀ x, 0 ≤ powerDensity α f x := fun x => Real.rpow_nonneg (norm_nonneg _) _
  obtain ⟨hs, he⟩ := standardRiesz_L1_domain_and_fourier hHLS.order_pos hHLS.order_lt_three hb h0 hp
  refine ⟨hs, ?_⟩
  rw [← hartree_energy_pair_identity hHLS hf]
  exact he

/-- Every actual compact density truncation has a finite standard-Riesz pair. -/
theorem hartree_truncated_standardRieszPair_integrable {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) {f : Space → ℂ}
    (hf : MemLp f 6 volume) (n : ℕ) :
    Integrable (standardRieszPair α (truncate (powerDensity α f) n)) (volume.prod volume) := by
  apply truncated_pair_integrable
  · exact (measurable_const.mul
      (((continuous_fst.sub continuous_snd).norm.measurable).pow_const (α-3))).aestronglyMeasurable
  · intro q
    unfold rieszKernel
    exact mul_nonneg hHLS.normalization_pos.le (Real.rpow_nonneg (norm_nonneg _) _)
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const (3+α)).aestronglyMeasurable
  · intro x
    exact Real.rpow_nonneg (norm_nonneg _) _
  · exact rieszPairDensity_integrable hHLS hf

/-- Actual L1 Fourier transforms are used only for the truncated densities. -/
theorem hartree_truncated_density_domain_and_fourier {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) {f : Space → ℂ}
    (hf : MemLp f 6 volume) (n : ℕ) :
    Integrable (fun ξ : Space => ‖ξ‖^(-α) *
      ‖paperFourier (truncate (powerDensity α f) n) ξ‖^2) volume ∧
    (∫ q, standardRieszPair α (truncate (powerDensity α f) n) q ∂volume.prod volume) =
      paperInverseFactor * ∫ ξ : Space, ‖ξ‖^(-α) *
        ‖paperFourier (truncate (powerDensity α f) n) ξ‖^2 := by
  apply standardRiesz_L1_domain_and_fourier hHLS.order_pos hHLS.order_lt_three
    (hartree_truncated_density_integrable α hf n)
  · exact truncate_nonneg (fun x => Real.rpow_nonneg (norm_nonneg (f x)) (3+α)) n
  · exact hartree_truncated_standardRieszPair_integrable hHLS hf n

/-- Spectral energies of the actual L1 density truncations converge to the original
physical Hartree energy. No classical Fourier transform of the non-L1 limit density is claimed. -/
theorem hartree_truncated_fourier_energy_tendsto {α : ℝ}
    (hHLS : OrdinaryHLS α (standardRieszConstant α)) {f : Space → ℂ}
    (hf : MemLp f 6 volume) :
    Tendsto (fun n : ℕ => paperInverseFactor * ∫ ξ : Space, ‖ξ‖^(-α) *
      ‖paperFourier (truncate (powerDensity α f) n) ξ‖^2) atTop
      (𝓝 (∫ x, potential α (standardRieszConstant α) f x * powerDensity α f x)) := by
  apply (hartree_density_truncation_tendsto hHLS hf).congr'
  exact Eventually.of_forall (fun n => (hartree_truncated_density_domain_and_fourier hHLS hf n).2)

#print axioms standardRiesz_L1_spectral_integrable
#print axioms standardRiesz_L1_fourier
#print axioms standardRiesz_L1_domain_and_fourier
#print axioms hartree_L1_density_domain_and_fourier
#print axioms hartree_truncated_standardRieszPair_integrable
#print axioms hartree_truncated_density_domain_and_fourier
#print axioms hartree_truncated_fourier_energy_tendsto
end HartreeF.HeatRiesz
