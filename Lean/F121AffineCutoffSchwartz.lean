import F121WeightedHighSmall
import FAffineSchwartzFree
import FCriticalAffineL2Continuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Paper121AffineCutoff
open EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest
open CriticalAffine FreeAffine Paper121SmallFrequency Paper121CutoffMaps

theorem lowSymbol_affine_scale (q : Cutoff) {a M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (ξ : Space) : lowSymbol q (M/a) (a⁻¹ • ξ) = lowSymbol q M ξ := by
  unfold lowSymbol
  rw [smul_smul]
  congr 2
  field_simp

theorem highSchwartz_affine (q : Cutoff) {a M : ℝ} (ha : 0 < a) (hM : 0 < M)
    (b : Space) (φ : Test) :
    highSchwartz q M (affineSchwartz ha b φ) =
      affineSchwartz ha b (highSchwartz q (M/a) φ) := by
  have hf : 𝓕 (highSchwartz q M (affineSchwartz ha b φ)) =
      𝓕 (affineSchwartz ha b (highSchwartz q (M/a) φ)) := by
    ext ξ
    rw [highSchwartz_fourier q hM, affineSchwartz_fourier, affineSchwartz_fourier,
      highSchwartz_fourier q (div_pos hM ha), lowSymbol_affine_scale q ha hM]
    simp only [Circle.smul_def, Complex.real_smul, smul_eq_mul]
    ring
  have he := congrArg (fun ψ : Test => 𝓕⁻ ψ) hf
  simpa only [fourierInv_fourier_eq] using he

theorem highEnergy_schwartz (hD : OrdinaryH1Density) {K : ℝ} (hS : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) (φ : Test) :
    highEnergyCLM hD hS q hM (schwartzEnergyState φ) =
      schwartzEnergyState (highSchwartz q M φ) := by
  apply energyDistribution_injective
  exact (highEnergyState_distribution hD hS q hM _).trans
    (highSchwartz_distribution q hM φ).symm

theorem affineSchwartz_L2 (a : ℝ) (ha : 0 < a) (b : Space) (φ : Test) :
    (affineSchwartz ha b φ).toLp 2 volume =
      a⁻¹ • gradientAffineL2 ha b (φ.toLp 2 volume) := by
  apply Lp.ext
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae (φ.coeFn_toLp 2 volume)
  filter_upwards [(affineSchwartz ha b φ).coeFn_toLp 2 volume,
    gradientAffineL2_ae ha b (φ.toLp 2 volume),
    Lp.coeFn_smul a⁻¹ (gradientAffineL2 ha b (φ.toLp 2 volume)), hi]
    with x ho hg hs hi
  rw [ho, hs]
  simp only [Pi.smul_apply]
  rw [hg]
  simp only [affineSchwartz_apply, valuePullback, gradientPullback, hi, smul_smul]
  rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]

theorem affineSchwartz_L2_norm {a : ℝ} (ha : 0 < a) (b : Space) (φ : Test) :
    ‖(affineSchwartz ha b φ).toLp 2 volume‖ = a⁻¹*‖φ.toLp 2 volume‖ := by
  rw [affineSchwartz_L2 a ha, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ha), (gradientAffineL2 ha b).norm_map]

end HartreeF.Paper121AffineCutoff
