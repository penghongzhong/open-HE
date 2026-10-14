import FAffineCanonicalPathSource

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Filter Set
open scoped ENNReal
namespace HartreeF.NonlinearAffine
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest ForcingDomain
open TimeHolder Retarded ActualDuhamelPath IntervalTimeTransport
open AffinePath AffineMixed AffineL1Source CriticalAffine
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalPathIntervalSource
  affineCriticalPath

variable (hDensity : OrdinaryH1Density) {K alpha kernel : ℝ} (hSob : OrdinarySobolev K)
  (hH : OrdinaryHLS alpha kernel) {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ)
  (hAB : A≤B) (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))

/-- Covariance of the SAME two actual scalar nonlinear source classes,
constructed from the original and transformed canonical paths. -/
theorem actual_nonlinear_source_value_ae : ∀ᵐ s ∂localMeasure A B,
    ((criticalPathIntervalSource hDensity hSob hH hAB
      (affineCriticalPath ha b c A B hAB u) 0).value s : Space → ℂ) =ᵐ[volume]
    (fun x => a^(5/2:ℝ) •
      (criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0).value
        (timeAffine a c s) (affine a b x)) := by
  have hE := (timeAffine_local_quasiMeasurePreserving ha c A B).ae
    (criticalPathIntervalSource_single_coeFn hDensity hSob hH (timeAffine_monotone ha c hAB) u)
  filter_upwards [hE,
    criticalPathIntervalSource_single_coeFn hDensity hSob hH hAB
      (affineCriticalPath ha b c A B hAB u),
    affine_path_forcing_ae (alpha := alpha) (kernel := kernel) ha b c A B hAB u] with s hs ht hF
  have hs' : ((criticalPathIntervalSource hDensity hSob hH
      (timeAffine_monotone ha c hAB) u 0).value (timeAffine a c s) : Space → ℂ) =ᵐ[volume]
      forcing alpha kernel (energyValue
        (extendEnergyPath (timeAffine_monotone ha c hAB) (energyPath _ u) (timeAffine a c s))) := hs
  have hp := ((affine_quasiMeasurePreserving ha.ne' b).ae_eq_comp hs').mono
    (fun x hx => congrArg (fun z : ℂ => a^(5/2:ℝ) • z) hx)
  exact ht.trans (hF.trans (Filter.EventuallyEq.symm hp))

/-- Equality of the actual constructed weak-gradient coordinates follows from
proved weak derivatives and scalar representatives, rather than a frame axiom. -/
theorem actual_nonlinear_source_gradient_ae : ∀ᵐ s ∂localMeasure A B, ∀ j : Fin 3,
    ((criticalPathIntervalSource hDensity hSob hH hAB
      (affineCriticalPath ha b c A B hAB u) 0).gradient j s : Space → ℂ) =ᵐ[volume]
    (fun x => a^(7/2:ℝ) •
      (criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0).gradient j
        (timeAffine a c s) (affine a b x)) := by
  have hG := (timeAffine_local_quasiMeasurePreserving ha c A B).ae
    (canonical_path_source_gradient_ae hDensity hSob hH (timeAffine_monotone ha c hAB) u)
  filter_upwards [hG,affine_path_source_canonical_gradient_ae hDensity hSob hH ha b c A B hAB u]
    with s hs ht
  intro j
  have hp := ((affine_quasiMeasurePreserving ha.ne' b).ae_eq_comp (hs j)).mono
    (fun x hx => congrArg (fun z : ℂ => a^(7/2:ℝ) • z) hx)
  exact (ht j).trans (Filter.EventuallyEq.symm hp)

/-- Reassembly retains the actual complex Euclidean vector, with its exact
amplitude; it is not replaced by a real-plus-imaginary norm estimate. -/
theorem actual_nonlinear_source_vector_ae : ∀ᵐ s ∂localMeasure A B,
    (fun x => (WithLp.toLp 2 (fun j : Fin 3 =>
      (criticalPathIntervalSource hDensity hSob hH hAB
        (affineCriticalPath ha b c A B hAB u) 0).gradient j s x) : EuclideanSpace ℂ (Fin 3))) =ᵐ[volume]
    (fun x => a^(7/2:ℝ) • (WithLp.toLp 2 (fun j : Fin 3 =>
      (criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0).gradient j
        (timeAffine a c s) (affine a b x)) : EuclideanSpace ℂ (Fin 3))) := by
  filter_upwards [actual_nonlinear_source_gradient_ae hDensity hSob hH ha b c A B hAB u] with s hs
  filter_upwards [ae_all_iff.mpr hs] with x hx
  exact PiLp.ext (fun j => hx j)

#print axioms actual_nonlinear_source_value_ae
#print axioms actual_nonlinear_source_gradient_ae
#print axioms actual_nonlinear_source_vector_ae
end HartreeF.NonlinearAffine
