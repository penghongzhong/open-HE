import FLowpassNoWasteTranspose

/-! A conditional native endpoint consumer. Its retained inputs are an actual
original L2_t L1_x source, an actual projected EndpointSource with a.e. same-symbol
binding and tail bound, original scalar no-waste, and the already retained ordinary
endpoint estimate. It constructs the lowpass and original L2 representatives;
it does not supply these inputs from the Hartree trajectory. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory FourierTransform Filter Set LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.MassRecovery
open Retarded EnergySpace EnergySpace.Highpass SobolevStretch StationarySelfTest

/-- Infinite half-line Riesz realization, not an asserted absolute Bochner integral. -/
def recoveredLowL2 {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) (G : EndpointSource) : L2 :=
  noWasteCoefficient σ • restrictedL2 hE (physicalTail σ t)
    (physicalTail_measurable σ t) (σ*t) (reflectedTail hσ t G)

theorem recoveredLowL2_norm {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) (G : EndpointSource) :
    ‖recoveredLowL2 hE hσ t G‖ ≤ C0 * tailNorm t G := by
  rw [recoveredLowL2, norm_smul, noWasteCoefficient_norm hσ, one_mul]
  exact (restrictedL2_norm hE _ _ _ _).trans_eq
    (congrArg (fun x : ℝ => C0 * x) (reflectedTail_norm hσ t G))

/-- The tested no-waste limit identifies the actual lowpass distribution with the
actual Riesz L2 output. No lowpass-L2 or original-L2 premise occurs. -/
theorem recoveredLowL2_distribution {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (F : EndpointOne) (G : EndpointSource)
    (hG : ∀ᵐ s ∂volume.restrict (Ici t),
      Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
    (hNW : OriginalScalarNoWaste σ t u F) :
    Lp.toTemperedDistribution (recoveredLowL2 hE hσ t G) = low q L (energyDistribution u) := by
  ext φ
  change ((Lp.toTemperedDistributionCLM ℂ volume 2)
    (noWasteCoefficient σ • restrictedL2 hE (physicalTail σ t)
      (physicalTail_measurable σ t) (σ*t) (reflectedTail hσ t G))) φ = _
  rw [map_smul]
  change noWasteCoefficient σ * Lp.toTemperedDistribution
    (restrictedL2 hE (physicalTail σ t) (physicalTail_measurable σ t)
      (σ*t) (reflectedTail hσ t G)) φ = _
  rw [restrictedL2_scalar]
  have hi := (hE.2 (physicalTail σ t) (physicalTail_measurable σ t)
    (σ*t) (reflectedTail hσ t G) φ).1
  exact tendsto_nhds_unique
    ((scalar_window_tendsto t _ hi).const_mul (noWasteCoefficient σ))
    (projected_scalar_noWaste q hL hσ t u F G hG hNW φ)

theorem recoveredLowL2_same_value (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (F : EndpointOne) (G : EndpointSource)
    (hG : ∀ᵐ s ∂volume.restrict (Ici t),
      Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
    (hNW : OriginalScalarNoWaste σ t u F) :
    (energyValue (lowEnergyState hDensity hSob q hL u) : V → ℂ) =ᵐ[volume]
      recoveredLowL2 hE hσ t G := by
  apply CriticalPathSpace.spatial_ae_eq_of_distribution_eq
  change energyDistribution (lowEnergyState hDensity hSob q hL u) = _
  rw [lowEnergyState_distribution, recoveredLowL2_distribution hE q hL hσ t u F G hG hNW]

theorem lowEnergyState_memLp_two_conditional (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (F : EndpointOne) (G : EndpointSource)
    (hG : ∀ᵐ s ∂volume.restrict (Ici t),
      Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
    (hNW : OriginalScalarNoWaste σ t u F) :
    MemLp (energyValue (lowEnergyState hDensity hSob q hL u) : V → ℂ) 2 volume :=
  (memLp_congr_ae (recoveredLowL2_same_value hDensity hSob hE q hL hσ t u F G hG hNW)).mpr
    (Lp.memLp _)

/-- Candidate for the same original state, from its actual high and recovered low values. -/
def recoveredValueL2 (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (G : EndpointSource) : L2 :=
  highValueL2 hDensity hSob q hL u + recoveredLowL2 hE hσ t G

theorem recoveredValueL2_distribution (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (F : EndpointOne) (G : EndpointSource)
    (hG : ∀ᵐ s ∂volume.restrict (Ici t),
      Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
    (hNW : OriginalScalarNoWaste σ t u F) :
    Lp.toTemperedDistribution (recoveredValueL2 hDensity hSob hE q hL hσ t u G) =
      energyDistribution u := by
  change (Lp.toTemperedDistributionCLM ℂ volume 2)
    (highValueL2 hDensity hSob q hL u + recoveredLowL2 hE hσ t G) = _
  rw [map_add]
  change Lp.toTemperedDistribution (highValueL2 hDensity hSob q hL u) +
    Lp.toTemperedDistribution (recoveredLowL2 hE hσ t G) = _
  rw [highValueL2_distribution, recoveredLowL2_distribution hE q hL hσ t u F G hG hNW]
  change energyDistribution u - low q L (energyDistribution u) + low q L (energyDistribution u) = _
  abel

theorem recoveredValueL2_same_value (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (F : EndpointOne) (G : EndpointSource)
    (hG : ∀ᵐ s ∂volume.restrict (Ici t),
      Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
    (hNW : OriginalScalarNoWaste σ t u F) :
    (recoveredValueL2 hDensity hSob hE q hL hσ t u G : V → ℂ) =ᵐ[volume] energyValue u :=
  CriticalPathSpace.spatial_ae_eq_of_distribution_eq _ _
    (recoveredValueL2_distribution hDensity hSob hE q hL hσ t u F G hG hNW)

theorem originalValue_memLp_two_conditional (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (F : EndpointOne) (G : EndpointSource)
    (hG : ∀ᵐ s ∂volume.restrict (Ici t),
      Lp.toTemperedDistribution (G s) = low q L (Lp.toTemperedDistribution (F s)))
    (hNW : OriginalScalarNoWaste σ t u F) : MemLp (energyValue u : V → ℂ) 2 volume :=
  (memLp_congr_ae (recoveredValueL2_same_value hDensity hSob hE q hL hσ t u F G hG hNW)).mp
    (Lp.memLp _)

theorem recoveredValueL2_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (G : EndpointSource) :
    ‖recoveredValueL2 hDensity hSob hE q hL hσ t u G‖ ≤
      L⁻¹ * pureGradientNorm u + C0 * tailNorm t G := by
  exact (norm_add_le _ _).trans (add_le_add
    (highValueL2_bound hDensity hSob q hL u) (recoveredLowL2_norm hE hσ t G))

/-- The Young/tail input is a quantitative bound on the specified actual source G. -/
theorem recoveredValueL2_mass_budget (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) {C0 : ℝ} (hE : OrdinaryEndpointBound C0)
    (q : Cutoff) {L : ℝ} (hL : 0 < L) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (t : ℝ) (u : EnergyState) (F : EndpointOne) (G : EndpointSource)
    {B CK : ℝ} (hB : pureGradientNorm u ≤ B)
    (hTail : tailNorm t G ≤ CK * Real.sqrt L * tailNorm t F) :
    ‖recoveredValueL2 hDensity hSob hE q hL hσ t u G‖ ≤
      B / L + (C0 * CK) * Real.sqrt L * tailNorm t F := by
  calc
    _ ≤ L⁻¹ * pureGradientNorm u + C0 * tailNorm t G :=
      recoveredValueL2_bound hDensity hSob hE q hL hσ t u G
    _ ≤ L⁻¹ * B + C0 * (CK * Real.sqrt L * tailNorm t F) :=
      add_le_add (mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hL.le))
        (mul_le_mul_of_nonneg_left hTail hE.1)
    _ = _ := by rw [div_eq_mul_inv]; ring

end HartreeF.MassRecovery
