import FActualAffineCriticalPath
import FAffineRetardedSourceIdentity
import FL1RetardedScalarIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.AffinePath
open EnergySpace CriticalPathSpace AffineMixed AffineL1Source CriticalAffine
open RawStabilityInputs ActualDuhamelPath IntervalTimeTransport Retarded FreeFlow
open SobolevStretch StationarySelfTest ActualStrichartz
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  affineCriticalPath parabolicCompactSource RawSpatialGradientSource.compactSource
  CompatibleL1IntervalSource.retardedCriticalPath

variable (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hStr : OrdinaryRetardedStrichartz h0 C)
    {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (hRaw : RawSpatialGradientSource I e G) {a : ℝ} (ha : 0<a) (b : Space)
    (c A B : ℝ) (hAB : A≤B) (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆ I)

/-- Pointwise distribution covariance, before using injectivity of the path graph. -/
theorem raw_retarded_affine_distribution (t : Icc A B) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _
      ((parabolicCompactSource hRaw ha b c A B hAB hI).retardedCriticalPath hDensity hSob h0 hStr) t) φ=
    energyDistribution (affineState ha b (energyPath _
      ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).retardedCriticalPath hDensity hSob h0 hStr)
      (intervalAffineHomeomorph ha c A B t))) φ := by
  have ht := (parabolicCompactSource hRaw ha b c A B hAB hI).retardedCriticalPath_scalar
    hDensity hSob h0 hStr t φ
  have hs := (hRaw.compactSource (timeAffine_monotone ha c hAB) hI).retardedCriticalPath_scalar
    hDensity hSob h0 hStr (intervalAffineHomeomorph ha c A B t) (dualAffineTest ha b φ)
  have hp := parabolicCompactSource_past_integral hRaw ha b c A B hAB hI (t:ℝ) φ
  have h := ht.trans (hp.trans hs.symm)
  exact h.trans (affineState_distribution ha b _ φ).symm

/-- Covariance of the actual constructed local retarded CriticalPath for the
same scalar-L1/vector-N raw source, through the literal past integral. -/
theorem raw_retarded_affine_covariance :
    (parabolicCompactSource hRaw ha b c A B hAB hI).retardedCriticalPath hDensity hSob h0 hStr=
      affineCriticalPath ha b c A B hAB
        ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).retardedCriticalPath hDensity hSob h0 hStr) := by
  apply energyPath_injective (intervalMeasure A B)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  ext φ
  rw [affineCriticalPath_energy_apply]
  exact raw_retarded_affine_distribution hDensity hSob h0 hStr hRaw ha b c A B hAB hI t φ

#print axioms raw_retarded_affine_distribution
#print axioms raw_retarded_affine_covariance
end HartreeF.AffinePath
