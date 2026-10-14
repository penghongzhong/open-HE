import FActualCriticalThreshold
import FSharpWFiniteSGlobalScattering

/-! R8.4 Theorem 1.1: the globality and scattering conclusion for the actual
canonical trajectory, with the original squared kinetic threshold.
The solution-class correspondence and the standard analytic interfaces require
separate semantic review. The theorem below retains no-bad-data explicitly;
it does not establish the unconditional manuscript theorem. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open Filter
open scoped Topology
namespace HartreeF.PaperMainEnvironment
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput
  ForcingDomain SharpOrdinary Regularization.Actual HeatRiesz
  ActualCriticalThreshold DynamicSharpW
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))

/-- The original two strict thresholds, for every homogeneous-energy datum.
There is no initial scalar mass, variance, radiality, or center premise. -/
def PaperThresholdConclusion : Prop :=
  ∀ u0 : EnergyState,
    totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha) →
    gradientSquared u0 < gradientSquared (normalizedBubbleState alpha) →
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 u0
    U.domain = Set.univ ∧ ∃ uMinus uPlus : EnergyState,
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0)

/-- Assembly into the manuscript's original threshold conclusion.
The additional `hNoBad` is the unresolved rigidity obligation, not a standard
analysis interface and not an accepted premise of R8.4 Theorem 1.1. -/
theorem paper_threshold_conclusion_of_no_bad
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing)
    (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (hNoBad : ¬ ∃ f, BadDatum hDensity hSob h0 hfree hret hefree heret hOrd f) :
    PaperThresholdConclusion hDensity hSob h0 hfree hret hefree heret hOrd := by
  intro u0 henergy hkinetic
  have hgradient : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha) :=
    (pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr hkinetic
  have hfinite : MaximalFiniteSGlobal.FiniteSOnDomain
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 u0) := by
    by_contra hnot
    exact hNoBad ⟨u0, ⟨henergy, hgradient⟩, hnot⟩
  obtain ⟨hglobal, uMinus, uPlus, _hem, hgm, _hep, hgp⟩ :=
    actualMaximalTrajectory_global_scattering_of_W_and_finiteS
      hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6
      0 u0 henergy hgradient hfinite
  exact ⟨hglobal, uMinus, uPlus, hgm, hgp⟩

end HartreeF.PaperMainEnvironment
