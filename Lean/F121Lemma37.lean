import F121Theorem36
import FActualDynamicSharpWTrapping

/-! Literal terminal wrapper for Lemma 3.7 of the 121-page manuscript:
the original strict W thresholds trap the actual maximal trajectory, and an
energy ceiling strictly below E(W) gives the displayed quantitative gap. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set
namespace HartreeF.Paper121Lemma37
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest Retarded
open ActualStrichartz EndpointOutput ForcingDomain Regularization.Actual
open MaximalTrajectory StateEnergy StateSharpThreshold StateSharpThresholdReview
open DynamicSharpW SharpOrdinary EnergyVariation

/-- The manuscript's inverse coercivity factor `2p/(p-1)`, with `p=3+alpha`. -/
def trappingFactor (alpha : ℝ) : ℝ := 2 * (3 + alpha) / (2 + alpha)

/-- The explicit gap attached to an energy ceiling `EStar`. -/
def trappingGap (alpha EStar : ℝ) : ℝ :=
  1 - (trappingFactor alpha * EStar /
    gradientSquared (normalizedBubbleState alpha)) ^ (2 + alpha)

/-- Scalar sharp-bound consequence used by the quantitative part of Lemma 3.7. -/
theorem interaction_gap_of_cap {p G A D B : ℝ}
    (hp : 1 < p) (hG : 0 < G) (hA : 0 ≤ A) (hAB : A ≤ B)
    (hD : D ≤ G ^ (1-p) * A ^ p) :
    D ≤ A * (B / G) ^ (p-1) := by
  have hB : 0 ≤ B := hA.trans hAB
  by_cases hz : A = 0
  · subst A
    simpa [Real.zero_rpow (by linarith : p ≠ 0)] using hD
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
  have hpow : A ^ p = A * A ^ (p-1) := by
    calc
      A ^ p = A ^ (1 + (p-1)) := by congr 1; ring
      _ = A ^ 1 * A ^ (p-1) := Real.rpow_add hAp _ _
      _ = A * A ^ (p-1) := by rw [Real.rpow_one]
  have hscale : G ^ (1-p) * B ^ (p-1) = (B/G) ^ (p-1) := by
    rw [Real.div_rpow hB hG.le]
    rw [show 1-p = -(p-1) by ring, Real.rpow_neg hG.le]
    ring
  calc
    D ≤ G ^ (1-p) * A ^ p := hD
    _ = A * (G ^ (1-p) * A ^ (p-1)) := by rw [hpow]; ring
    _ ≤ A * (G ^ (1-p) * B ^ (p-1)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hA hAB (by linarith)) (Real.rpow_nonneg hG.le _)
    _ = A * (B/G) ^ (p-1) := by rw [hscale]

/-- Full Lemma 3.7 on the complete actual maximal lifespan.  Besides the
conserved energy and kinetic cap it records the manuscript's explicit
`delta_*`, the coercive difference `A-D`, and the zero-energy endpoint. -/
theorem lemma37_original_threshold_trapping
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hSharpHLS : SharpOrdinaryHLS alpha) (hSharpSob : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (s0 : ℝ) (u0 : EnergyState)
    (henergy : totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hgradient : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha)) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret
      hefree heret hOrd s0 u0
    (∀ t ∈ M.domain, totalEnergy alpha (M.state t) = totalEnergy alpha u0) ∧
    (∀ t ∈ M.domain,
      gradientSquared (M.state t) ≤ trappingFactor alpha * totalEnergy alpha u0 ∧
      trappingFactor alpha * totalEnergy alpha u0 <
        gradientSquared (normalizedBubbleState alpha)) ∧
    (∀ EStar : ℝ, 0 ≤ EStar →
      EStar < totalEnergy alpha (normalizedBubbleState alpha) →
      totalEnergy alpha u0 ≤ EStar →
      0 < trappingGap alpha EStar ∧
      ∀ t ∈ M.domain,
        trappingGap alpha EStar * gradientSquared (M.state t) ≤
          gradientSquared (M.state t) - interactionLp alpha (energyValue (M.state t))) ∧
    (u0 ≠ 0 → 0 < totalEnergy alpha u0) ∧
    (totalEnergy alpha u0 = 0 → u0 = 0) := by
  dsimp only
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret
    hefree heret hOrd s0 u0
  have hfactor : 0 < trappingFactor alpha := by
    unfold trappingFactor
    exact div_pos (by linarith [hSharpHLS.order_pos])
      (by linarith [hSharpHLS.order_pos])
  have hWkin : 0 < gradientSquared (normalizedBubbleState alpha) := by
    rw [normalizedBubbleState_kinetic hSharpHLS.order_pos hSharpHLS.order_lt_three]
    exact standardCombinedThreshold_pos hSharpHLS.order_pos hSharpHLS.order_lt_three
  have htrap := actualMaximalTrajectory_sharp_W_trapping hDensity hSob h0 hfree hret
    hefree heret hOrd hSharpHLS hSharpSob S Bw Bs B6 s0 u0 henergy hgradient
  refine ⟨actualMaximalTrajectory_totalEnergy_constant hDensity hSob h0 hfree hret
      hefree heret hOrd S Bw Bs B6 s0 u0, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [trappingFactor] using htrap t ht
  · intro EStar hEStar hEStarW huE
    let q := trappingFactor alpha * EStar /
      gradientSquared (normalizedBubbleState alpha)
    have hq0 : 0 ≤ q := div_nonneg (mul_nonneg hfactor.le hEStar) hWkin.le
    have hscaledW : trappingFactor alpha *
        totalEnergy alpha (normalizedBubbleState alpha) =
        gradientSquared (normalizedBubbleState alpha) := by
      simpa only [trappingFactor] using
        normalizedBubbleState_scaled_energy hOrd hSharpHLS hSharpSob hDensity
    have hq1 : q < 1 := by
      apply (div_lt_one hWkin).mpr
      rw [← hscaledW]
      exact mul_lt_mul_of_pos_left hEStarW hfactor
    have hpow1 : q ^ (2+alpha) < 1 :=
      Real.rpow_lt_one hq0 hq1 (by linarith [hSharpHLS.order_pos])
    refine ⟨by dsimp [trappingGap, q] at hpow1 ⊢; linarith, ?_⟩
    intro t ht
    have hAt := (htrap t ht).1
    have hcap : gradientSquared (M.state t) ≤ trappingFactor alpha * EStar :=
      hAt.trans (mul_le_mul_of_nonneg_left huE hfactor.le)
    have hD := state_sharp_interaction_bound hOrd hSharpHLS hSharpSob (M.state t)
    have hgap := interaction_gap_of_cap
      (p := 3+alpha)
      (G := gradientSquared (normalizedBubbleState alpha))
      (A := gradientSquared (M.state t))
      (D := interactionLp alpha (energyValue (M.state t)))
      (B := trappingFactor alpha * EStar)
      (by linarith [hSharpHLS.order_pos]) hWkin
      (gradientSquared_nonneg (M.state t)) hcap (by
        rw [normalizedBubbleState_kinetic hSharpHLS.order_pos hSharpHLS.order_lt_three]
        simpa only [show 1-(3+alpha) = 1-(3+alpha) by rfl] using hD)
    rw [show 3+alpha-1 = 2+alpha by ring] at hgap
    dsimp [trappingGap, q] at hgap ⊢
    linarith
  · intro hne
    have hA : gradientSquared u0 ≤ gradientSquared (normalizedBubbleState alpha) :=
      (pureGradientNorm_lt_iff_gradientSquared_lt u0
        (normalizedBubbleState alpha)).mp hgradient |>.le
    have hz := state_eq_zero_of_nonpositive_energy_below_W hOrd hSharpHLS hSharpSob u0 hA
    exact lt_of_not_ge (fun hnonpos ↦ hne (hz hnonpos))
  · intro hzero
    have hA : gradientSquared u0 ≤ gradientSquared (normalizedBubbleState alpha) :=
      (pureGradientNorm_lt_iff_gradientSquared_lt u0
        (normalizedBubbleState alpha)).mp hgradient |>.le
    exact state_eq_zero_of_nonpositive_energy_below_W hOrd hSharpHLS hSharpSob u0 hA hzero.le

#print axioms interaction_gap_of_cap
#print axioms lemma37_original_threshold_trapping
end HartreeF.Paper121Lemma37
