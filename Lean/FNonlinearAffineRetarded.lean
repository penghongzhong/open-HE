import FNonlinearAffinePastIntegral

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Set
namespace HartreeF.NonlinearAffine
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest ForcingDomain
open TimeHolder Retarded ActualStrichartz ActualDuhamelPath IntervalTimeTransport
open AffinePath AffineMixed CriticalAffine
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  criticalPathIntervalSource affineCriticalPath intervalRetardedCriticalPath

variable (hDensity : OrdinaryH1Density) {K C0 Cr alpha kernel : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
  {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
  (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))

/-- The existing nonlinear retarded constructor is applied to its two produced
sources. There is no scalar-time2 source hypothesis on external data. -/
theorem nonlinear_retarded_affine_distribution (t : Icc A B) (φ : FreeFlow.Test) :
    energyDistribution (energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 hret
      (criticalPathIntervalSource hDensity hSob hH hAB
        (affineCriticalPath ha b c A B hAB u) 0)) t) φ=
    energyDistribution (affineState ha b (energyPath _
      (intervalRetardedCriticalPath hDensity hSob h0 hret
        (criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0))
      (intervalAffineHomeomorph ha c A B t))) φ := by
  have ht := intervalRetardedCriticalPath_scalar hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hAB (affineCriticalPath ha b c A B hAB u) 0) t φ
  have hs := intervalRetardedCriticalPath_scalar hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0)
    (intervalAffineHomeomorph ha c A B t) (dualAffineTest ha b φ)
  have hp := nonlinear_source_past_integral hDensity hSob hH ha b c A B hAB u (t:ℝ) φ
  exact (ht.trans (hp.trans hs.symm)).trans (affineState_distribution ha b _ φ).symm

theorem nonlinear_retarded_affine_covariance :
    intervalRetardedCriticalPath hDensity hSob h0 hret
      (criticalPathIntervalSource hDensity hSob hH hAB (affineCriticalPath ha b c A B hAB u) 0)=
    affineCriticalPath ha b c A B hAB
      (intervalRetardedCriticalPath hDensity hSob h0 hret
        (criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0)) := by
  apply energyPath_injective (intervalMeasure A B)
  apply ContinuousMap.ext
  intro t
  apply energyDistribution_injective
  ext φ
  rw [affineCriticalPath_energy_apply]
  exact nonlinear_retarded_affine_distribution hDensity hSob h0 hret hH ha b c A B hAB u t φ

#print axioms nonlinear_retarded_affine_distribution
#print axioms nonlinear_retarded_affine_covariance
end HartreeF.NonlinearAffine
