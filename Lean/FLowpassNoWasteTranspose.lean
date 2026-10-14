import FEndpointSourceReflection
import FHighpassContraction

/-! Exact lowpass transpose and the original finite no-waste sequence.
The inputs are actual L2_t L1_x / L2_t L6/5_x classes with an a.e. same-symbol
source identity. Neither lowpass output nor original value L2 is an input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.MassRecovery
open Retarded FreeFlow EnergySpace.Highpass

/-- Transpose for the actual complex-bilinear distribution convention. -/
def lowTest (q : Cutoff) (L : ℝ) : Test →L[ℂ] Test :=
  fourierCLM ℂ Test ∘L SchwartzMap.smulLeftCLM ℂ (lowSymbol q L) ∘L fourierInvCLM ℂ Test

theorem low_apply (q : Cutoff) (L : ℝ) (D : TD) (φ : Test) :
    low q L D φ = D (lowTest q L φ) := rfl

theorem low_free_comm (q : Cutoff) {L : ℝ} (hL : 0 < L) (τ : ℝ) (D : TD) :
    low q L (free τ D) = free τ (low q L D) := by
  unfold low free
  rw [TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (phase_temperate τ) (lowSymbol_temperate q hL),
    TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (lowSymbol_temperate q hL) (phase_temperate τ)]
  rw [mul_comm (phase τ) (lowSymbol q L)]

theorem low_free_test (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (τ : ℝ) (D : TD) (φ : Test) :
    low q L D (freeTest τ φ) = D (freeTest τ (lowTest q L φ)) := by
  calc
    _ = free τ (low q L D) φ := rfl
    _ = low q L (free τ D) φ := congrArg (fun Z : TD => Z φ) (low_free_comm q hL τ D).symm
    _ = _ := rfl

def noWasteCoefficient (σ : ℝ) : ℂ := -Complex.I * (σ : ℂ)

theorem noWasteCoefficient_norm {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ‖noWasteCoefficient σ‖ = 1 := by
  rcases hσ with rfl | rfl <;> simp [noWasteCoefficient]

/-- Original, unprojected tested no-waste, on the same absolute sequence n+1. -/
def OriginalScalarNoWaste (σ t : ℝ) (u : EnergySpace.EnergyState) (F : EndpointOne) : Prop :=
  ∀ φ : Test, Tendsto (fun n : ℕ => noWasteCoefficient σ *
    ∫ s in Icc t (n + 1), Lp.toTemperedDistribution (F s) (freeTest (σ * (t-s)) φ))
    atTop (𝓝 (EnergySpace.energyDistribution u φ))

/-- Actual reflection of source and time window; absolute Jacobian is one. -/
theorem reflected_window_scalar {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t T : ℝ) (G : EndpointSource) (φ : Test) :
    (∫ y in physicalWindow σ t T,
      scalarIntegrand (σ*t) (reflectedTail hσ t G) φ y) =
      ∫ s in Icc t T, Lp.toTemperedDistribution (G s) (freeTest (σ*(t-s)) φ) := by
  calc
    _ = ∫ y in physicalWindow σ t T,
        Lp.toTemperedDistribution (G (timeSign σ y))
          (freeTest (σ * (t - timeSign σ y)) φ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (reflectedTail_coe hσ t G),
        ae_restrict_mem (physicalWindow_measurable σ t T)] with y hG hy
      have ht : timeSign σ y ∈ Ici t := hy.1
      have he : σ*t-y = σ*(t-timeSign σ y) := by
        rcases hσ with rfl | rfl
        · simp [timeSign]
        · simp [timeSign, sub_eq_add_neg, add_comm]
      change Lp.toTemperedDistribution (reflectedTail hσ t G y) (freeTest (σ*t-y) φ) = _
      rw [hG, indicator_of_mem ht, he]
    _ = _ := (timeSign_preserving hσ).setIntegral_preimage_emb
      (timeSign_embedding hσ)
      (fun s => Lp.toTemperedDistribution (G s) (freeTest (σ*(t-s)) φ)) (Icc t T)

/-- A.e. equality of actual projected sources is transported through the actual free group. -/
theorem low_source_window (q : Cutoff) {L : ℝ} (hL : 0 < L)
    (σ t T : ℝ) (F : EndpointOne) (G : EndpointSource)
    (hG : ∀ᵐ s ∂volume.restrict (Ici t),
      Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
    (φ : Test) :
    (∫ s in Icc t T, Lp.toTemperedDistribution (G s) (freeTest (σ*(t-s)) φ)) =
      ∫ s in Icc t T, Lp.toTemperedDistribution (F s)
        (freeTest (σ*(t-s)) (lowTest q L φ)) := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset
    (show Icc t T ⊆ Ici t from fun _ h => h.1) hG] with s hs
  rw [hs]
  exact low_free_test q hL _ _ _

theorem projected_scalar_noWaste (q : Cutoff) {L : ℝ} (hL : 0 < L)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) (u : EnergySpace.EnergyState)
    (F : EndpointOne) (G : EndpointSource)
    (hG : ∀ᵐ s ∂volume.restrict (Ici t),
      Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
    (hNW : OriginalScalarNoWaste σ t u F) (φ : Test) :
    Tendsto (fun n : ℕ => noWasteCoefficient σ *
      ∫ y in physicalWindow σ t (n+1), scalarIntegrand (σ*t) (reflectedTail hσ t G) φ y)
      atTop (𝓝 (low q L (EnergySpace.energyDistribution u) φ)) := by
  have h := hNW (lowTest q L φ)
  change Tendsto _ atTop (𝓝 (low q L (EnergySpace.energyDistribution u) φ)) at h
  convert h using 1
  funext n
  rw [reflected_window_scalar hσ, low_source_window q hL σ t (n+1) F G hG]

end HartreeF.MassRecovery
