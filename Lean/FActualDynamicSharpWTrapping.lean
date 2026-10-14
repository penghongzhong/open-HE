import FSharpWStateTopology
import FLocalMildTrajectoryEnergyConservation
import FActualMaximalMildTrajectory
import FStateSharpThresholdReviewConsumers

/-! The original strict energy and homogeneous gradient thresholds at the
actual W imply uniform trapping for the actual mild solution throughout its
own lifespan. Conservation is consumed from its proved native theorem.
Neither conservation, a kinetic cap, nor an L2 condition on u0 is a premise. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.DynamicSharpW
open EnergySpace CriticalPathSpace StateEnergy StateSharpThreshold MaximalTrajectory EnergyVariation
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain EndpointOutput
open Regularization.Actual SharpOrdinary DirectionalCoercivity HeatRiesz BubbleProfile
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyValue
  actualMaximalTrajectory

/-- Dynamic trapping on the entire native connected lifespan, with p=3+alpha
and exactly the normalized ground state's original kinetic and energy levels. -/
theorem localMildTrajectory_sharp_W_trapping (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha s0 : ℝ} {u0 : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (U : LocalMildTrajectory alpha (standardRieszConstant alpha) s0 u0)
    (henergy : totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hgradient : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha)) :
    ∀ t ∈ U.domain,
      gradientSquared (U.state t) ≤ (2*(3+alpha)/(2+alpha))*totalEnergy alpha u0 ∧
      (2*(3+alpha)/(2+alpha))*totalEnergy alpha u0 <
        gradientSquared (normalizedBubbleState alpha) := by
  have hcont : ContinuousOn (fun t => gradientSquared (U.state t)) U.domain :=
    gradientSquared_continuous.comp_continuousOn U.continuous
  have hinit : gradientSquared (U.state s0) < standardCombinedThreshold alpha := by
    rw [U.initial, ← normalizedBubbleState_kinetic hH.order_pos hH.order_lt_three]
    exact (pureGradientNorm_lt_iff_gradientSquared_lt _ _).mp hgradient
  have hgap : totalEnergy alpha u0 <
      (((3+alpha)-1)/(2*(3+alpha))) * standardCombinedThreshold alpha := by
    rw [normalizedBubbleState_energy hOrd hH hS hDensity] at henergy
    simpa only [thresholdEnergy, show 3+alpha-1 = 2+alpha by ring] using henergy
  have hE : ∀ t ∈ U.domain, totalEnergy alpha u0 =
      gradientSquared (U.state t)/2 -
        interactionLp alpha (energyValue (U.state t))/(2*(3+alpha)) := by
    intro t ht
    exact (LocalMildTrajectory.totalEnergy_constant_on_domain hDensity hSob h0 hfree hret
      hefree heret hOrd S Bw Bs B6 U ht).symm
  have htrap := EnergyTrapping.sharp_energy_trapping U.domain_connected hcont
    (p := 3+alpha) (G := standardCombinedThreshold alpha) (E := totalEnergy alpha u0)
    (by linarith [hH.order_pos]) (standardCombinedThreshold_pos hH.order_pos hH.order_lt_three)
    U.center_mem hinit (fun t _ => gradientSquared_nonneg (U.state t))
    (fun t _ => state_sharp_interaction_bound hOrd hH hS (U.state t)) hE hgap
  intro t ht
  simpa only [show 3+alpha-1 = 2+alpha by ring,
    normalizedBubbleState_kinetic hH.order_pos hH.order_lt_three] using htrap t ht

/-- The original two thresholds produce the quantitative pure dotH1 cap;
the cap itself is a conclusion and is strictly below the same W norm. -/
theorem localMildTrajectory_pureGradient_cap (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha s0 : ℝ} {u0 : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (U : LocalMildTrajectory alpha (standardRieszConstant alpha) s0 u0)
    (henergy : totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hgradient : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha)) :
    ∀ t ∈ U.domain,
      pureGradientNorm (U.state t) ≤
        Real.sqrt ((2*(3+alpha)/(2+alpha))*totalEnergy alpha u0) ∧
      Real.sqrt ((2*(3+alpha)/(2+alpha))*totalEnergy alpha u0) <
        pureGradientNorm (normalizedBubbleState alpha) := by
  intro t ht
  obtain ⟨hcap, hstrict⟩ := localMildTrajectory_sharp_W_trapping hDensity hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 U henergy hgradient t ht
  exact ⟨pureGradientNorm_le_of_gradientSquared_le _ hcap,
    (Real.sqrt_lt_sqrt_iff ((gradientSquared_nonneg (U.state t)).trans hcap)).mpr hstrict⟩

/-- Direct specialization to the constructed actual maximal solution, without
any abstract trajectory or conservation/cap parameter in the public result. -/
theorem actualMaximalTrajectory_sharp_W_trapping (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (s0 : ℝ) (u0 : EnergyState)
    (henergy : totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hgradient : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha)) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
    ∀ t ∈ U.domain,
      gradientSquared (U.state t) ≤ (2*(3+alpha)/(2+alpha))*totalEnergy alpha u0 ∧
      (2*(3+alpha)/(2+alpha))*totalEnergy alpha u0 <
        gradientSquared (normalizedBubbleState alpha) :=
  localMildTrajectory_sharp_W_trapping hDensity hSob h0 hfree hret hefree heret hOrd hH hS
    S Bw Bs B6 (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0)
    henergy hgradient

/-- Uniform pure homogeneous gradient control derived from the two original
W thresholds for the actual maximal solution at the original EnergyState. -/
theorem actualMaximalTrajectory_pureGradient_cap (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (s0 : ℝ) (u0 : EnergyState)
    (henergy : totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hgradient : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha)) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
    ∀ t ∈ U.domain,
      pureGradientNorm (U.state t) ≤
        Real.sqrt ((2*(3+alpha)/(2+alpha))*totalEnergy alpha u0) ∧
      Real.sqrt ((2*(3+alpha)/(2+alpha))*totalEnergy alpha u0) <
        pureGradientNorm (normalizedBubbleState alpha) :=
  localMildTrajectory_pureGradient_cap hDensity hSob h0 hfree hret hefree heret hOrd hH hS
    S Bw Bs B6 (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0)
    henergy hgradient

/-- A genuine least-energy weak stationary ground state has exactly the same
levels as normalized W. No classification of all sharp optimizers is used. -/
theorem actualMaximalTrajectory_groundState_trapping (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    {w : Space → ℂ} {WRe WIm : Space → Space} (hw : IsGroundState alpha w WRe WIm)
    (s0 : ℝ) (u0 : EnergyState)
    (henergy : totalEnergy alpha u0 < energy alpha w WRe WIm)
    (hgradient : pureGradientNorm u0 < Real.sqrt (kinetic WRe WIm)) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
    ∀ t ∈ U.domain,
      gradientSquared (U.state t) ≤ (2*(3+alpha)/(2+alpha))*totalEnergy alpha u0 ∧
      (2*(3+alpha)/(2+alpha))*totalEnergy alpha u0 < kinetic WRe WIm := by
  have hlevels := StateSharpThresholdReview.canonical_groundState_levels hw hOrd hH hS hDensity
  have hkin : kinetic WRe WIm = gradientSquared (normalizedBubbleState alpha) := by
    simpa only [gradientSquared_inDotEnergyState] using hlevels.1
  have henergy' : totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha) := by
    rw [← hlevels.2, totalEnergy_inDotEnergyState]
    exact henergy
  have hgradient' : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha) := by
    simpa only [hkin, pureGradientNorm] using hgradient
  dsimp only
  intro t ht
  simpa only [hkin] using actualMaximalTrajectory_sharp_W_trapping hDensity hSob h0 hfree hret
    hefree heret hOrd hH hS S Bw Bs B6 s0 u0 henergy' hgradient' t ht

/-- The literal paper data u0 with only L6 and weak L2 gradients enters the
constructed maximal flow by the exact native state map. Both original strict
thresholds and the resulting a priori kinetic cap retain their exact values. -/
theorem actualMaximalTrajectory_original_groundState_trapping (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    {w : Space → ℂ} {WRe WIm : Space → Space} (hw : IsGroundState alpha w WRe WIm)
    (s0 : ℝ) {u : Space → ℂ} {URe UIm : Space → Space} (hu : InDotH1 u URe UIm)
    (henergy : energy alpha u URe UIm < energy alpha w WRe WIm)
    (hgradient : Real.sqrt (kinetic URe UIm) < Real.sqrt (kinetic WRe WIm)) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0
      (inDotEnergyState hu)
    ∀ t ∈ M.domain,
      gradientSquared (M.state t) ≤ (2*(3+alpha)/(2+alpha))*energy alpha u URe UIm ∧
      (2*(3+alpha)/(2+alpha))*energy alpha u URe UIm < kinetic WRe WIm := by
  have he : totalEnergy alpha (inDotEnergyState hu) < energy alpha w WRe WIm := by
    simpa only [totalEnergy_inDotEnergyState] using henergy
  have hg : pureGradientNorm (inDotEnergyState hu) < Real.sqrt (kinetic WRe WIm) := by
    simpa only [pureGradientNorm, gradientSquared_inDotEnergyState] using hgradient
  simpa only [totalEnergy_inDotEnergyState] using
    actualMaximalTrajectory_groundState_trapping hDensity hSob h0 hfree hret hefree heret
      hOrd hH hS S Bw Bs B6 hw s0 (inDotEnergyState hu) he hg

#print axioms localMildTrajectory_sharp_W_trapping
#print axioms localMildTrajectory_pureGradient_cap
#print axioms actualMaximalTrajectory_sharp_W_trapping
#print axioms actualMaximalTrajectory_pureGradient_cap
#print axioms actualMaximalTrajectory_groundState_trapping
#print axioms actualMaximalTrajectory_original_groundState_trapping
end HartreeF.DynamicSharpW
