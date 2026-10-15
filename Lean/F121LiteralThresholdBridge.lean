import F121LiteralSolutionClass
import F121GlobalCritical

/-! The original threshold conclusion, with the competing literal solution
class and global maximality spelled out, is equivalent to the canonical
threshold interface. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121LiteralThreshold
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput
  ForcingDomain HeatRiesz PaperMainEnvironment Paper121LiteralClass
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

def LiteralThresholdConclusion (hDensity : OrdinaryH1Density)
    {K alpha : ℝ} (hSob : OrdinarySobolev K) : Prop :=
  ∀ f : EnergyState,
    totalEnergy alpha f < totalEnergy alpha (normalizedBubbleState alpha) →
    gradientSquared f < gradientSquared (normalizedBubbleState alpha) →
    ∃ U : LiteralLocalSolution alpha (standardRieszConstant alpha) 0 f,
      U.domain = univ ∧
      (∀ V : LiteralLocalSolution alpha (standardRieszConstant alpha) 0 f,
        V.domain ⊆ U.domain ∧ EqOn U.state V.state V.domain) ∧
      ∃ uMinus uPlus : EnergyState,
        Tendsto (fun t : ℝ => pureGradientNorm
          (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
        Tendsto (fun t : ℝ => pureGradientNorm
          (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0)

theorem threshold_conclusion_iff_literal (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha)) :
    PaperThresholdConclusion hDensity hSob h0 hfree hret hefree heret hOrd ↔
      LiteralThresholdConclusion hDensity (alpha := alpha) hSob := by
  constructor
  · intro h f hE hG
    obtain ⟨hg, uMinus, uPlus, hm, hp⟩ := h f hE hG
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    refine ⟨ofNative M, hg, ?_, uMinus, uPlus, hm, hp⟩
    intro V
    have hV := actual_maximal_among_literal_solutions
      hDensity hSob h0 hfree hret hefree heret hOrd 0 f V
    exact ⟨hV.1, hV.2.1⟩
  · intro h f hE hG
    obtain ⟨U, hU, _hmax, uMinus, uPlus, hm, hp⟩ := h f hE hG
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
    have hUM := actual_maximal_among_literal_solutions
      hDensity hSob h0 hfree hret hefree heret hOrd 0 f U
    have hg : M.domain = univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro t
      exact hUM.1 (by rw [hU]; trivial)
    have heq : M.state = U.state := by
      funext t
      exact hUM.2.1 (by rw [hU]; trivial)
    refine ⟨hg, uMinus, uPlus, ?_, ?_⟩
    · change Tendsto (fun t : ℝ => pureGradientNorm
        (M.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0)
      simpa only [heq] using hm
    · change Tendsto (fun t : ℝ => pureGradientNorm
        (M.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0)
      simpa only [heq] using hp

open MaximalFiniteSGlobal SharpOrdinary Regularization.Actual R2SquareTail CriticalAffine
  ProfileEnergy ActualProfileEnergy ActualCriticalThreshold DynamicSharpW LocalRellich LinearWeakEquation
  ActualNativeOrbitWindows ActualCompactOrbitGauge ActualBilateralCriticalProfile

theorem global_critical_element_of_literal_threshold_failure
    (hDensity : OrdinaryH1Density) (hRel : OrdinaryRellichBall)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hExtract : OrdinaryLinearProfileExtraction hDensity hSob)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (cutoff : Highpass.Cutoff)
    (hfailure : ¬ LiteralThresholdConclusion hDensity (alpha := alpha) hSob) :
    let Ec := criticalLevel hDensity hSob h0 hfree hret hefree heret hOrd
    0 < Ec ∧ Ec < totalEnergy alpha (normalizedBubbleState alpha) ∧
      ∃ psi : EnergyState, psi ≠ 0 ∧ totalEnergy alpha psi = Ec ∧ StableDatum alpha psi ∧
        let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 psi
        V.domain = univ ∧
        (∀ t : ℝ,
          TimeHolder.mixedNorm (volume.restrict (Ici t)) volume 10 10
              (fun z => energyValue (V.state z)) = ∞ ∧
          TimeHolder.mixedNorm (volume.restrict (Iic t)) volume 10 10
              (fun z => energyValue (V.state z)) = ∞) ∧
        (∀ t : ℝ, totalEnergy alpha (V.state t) = Ec ∧
          2 * Ec ≤ gradientSquared (V.state t) ∧
          gradientSquared (V.state t) ≤ kappa alpha*Ec ∧
          kappa alpha*Ec < gradientSquared (normalizedBubbleState alpha)) ∧
        ∃ (r : ℝ → ℝ) (hr : ∀ t, 0 < r t) (y : ℝ → Space) (Q : Set EnergyState),
          IsCompact Q ∧ Q.Nonempty ∧ (0 : EnergyState) ∉ Q ∧
          (∀ q ∈ Q, totalEnergy alpha q = Ec ∧
            2 * Ec ≤ gradientSquared q ∧
            gradientSquared q ≤ kappa alpha*Ec ∧
            gradientSquared q < gradientSquared (normalizedBubbleState alpha) ∧
            totalEnergy alpha q < totalEnergy alpha (normalizedBubbleState alpha)) ∧
          (∀ t : ℝ,
            (criticalAffineState (r t) (hr t) (y t)).symm (V.state t) ∈ Q) ∧
          IsCompact (closure {q : EnergyState | ∃ t ∈ V.domain,
            q = (criticalAffineState (r t) (hr t) (y t)).symm (V.state t)}) := by
  apply Paper121GlobalCritical.global_critical_element_of_threshold_failure
    hDensity hRel hSob h0 hfree hret hefree heret hOrd hH hS
    S Bw Bs B6 hExtract hgen hUnique cutoff
  intro h
  exact hfailure ((threshold_conclusion_iff_literal
    hDensity hSob h0 hfree hret hefree heret hOrd).mp h)

end HartreeF.Paper121LiteralThreshold
