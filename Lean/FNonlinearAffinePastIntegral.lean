import FActualNonlinearSourceCovariance
import FAffineRetardedSourceIdentity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal
namespace HartreeF.NonlinearAffine
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest ForcingDomain
open TimeHolder Retarded ActualDuhamelPath IntervalTimeTransport
open AffinePath AffineMixed CriticalAffine
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalPathIntervalSource
  affineCriticalPath

variable (hDensity : OrdinaryH1Density) {K alpha kernel : ℝ} (hSob : OrdinarySobolev K)
  (hH : OrdinaryHLS alpha kernel) {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ)
  (hAB : A≤B) (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))

/-- Literal tested integrand covariance for the two produced nonlinear sources. -/
theorem nonlinear_source_integrand_ae (t : ℝ) (φ : FreeFlow.Test) : ∀ᵐ s ∂localMeasure A B,
    Lp.toTemperedDistribution ((criticalPathIntervalSource hDensity hSob hH hAB
      (affineCriticalPath ha b c A B hAB u) 0).value s) (freeTest (t-s) φ)=
    a^2 • Lp.toTemperedDistribution
      ((criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0).value
        (timeAffine a c s))
      (freeTest (timeAffine a c t-timeAffine a c s) (dualAffineTest ha b φ)) := by
  filter_upwards [actual_nonlinear_source_value_ae hDensity hSob hH ha b c A B hAB u] with s hs
  have ht : timeAffine a c t-timeAffine a c s=a^2*(t-s) := by unfold timeAffine; ring
  simp only [Lp.toTemperedDistribution_apply,smul_eq_mul]
  rw [ht]
  calc
    _ = ∫ x, freeTest (t-s) φ x * parabolicField a b c (5/2)
        (fun r => (criticalPathIntervalSource hDensity hSob hH
          (timeAffine_monotone ha c hAB) u 0).value r) s x := by
      apply integral_congr_ae
      exact hs.mono (fun x hx => congrArg (fun z : ℂ => freeTest (t-s) φ x*z) hx)
    _ = a^2 • ∫ x, dualAffineTest ha b (freeTest (t-s) φ) x *
        (criticalPathIntervalSource hDensity hSob hH
          (timeAffine_monotone ha c hAB) u 0).value (timeAffine a c s) x :=
      parabolicSource_spatial_pairing ha b c _ s (freeTest (t-s) φ)
    _ = _ := by rw [dualAffineTest_freeTest]

/-- The scalar nonlinear source factor cancels the positive time Jacobian.
Both source classes are constructed from actual paths, not assumed inputs. -/
theorem nonlinear_source_past_integral (t : ℝ) (φ : FreeFlow.Test) :
    (∫ s in Icc A B ∩ Iio t,
      Lp.toTemperedDistribution ((criticalPathIntervalSource hDensity hSob hH hAB
        (affineCriticalPath ha b c A B hAB u) 0).value s) (freeTest (t-s) φ))=
    ∫ r in Icc (timeAffine a c A) (timeAffine a c B) ∩ Iio (timeAffine a c t),
      Lp.toTemperedDistribution
        ((criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0).value r)
        (freeTest (timeAffine a c t-r) (dualAffineTest ha b φ)) := by
  have he := ae_mono (Measure.restrict_mono_set volume
    (show Icc A B ∩ Iio t ⊆ Icc A B from inter_subset_left))
    (nonlinear_source_integrand_ae hDensity hSob hH ha b c A B hAB u t φ)
  calc
    _ = ∫ s in Icc A B ∩ Iio t,
        a^2 • Lp.toTemperedDistribution
          ((criticalPathIntervalSource hDensity hSob hH
            (timeAffine_monotone ha c hAB) u 0).value (timeAffine a c s))
          (freeTest (timeAffine a c t-timeAffine a c s) (dualAffineTest ha b φ)) := integral_congr_ae he
    _ = a^2 • ∫ s in Icc A B ∩ Iio t,
        Lp.toTemperedDistribution
          ((criticalPathIntervalSource hDensity hSob hH
            (timeAffine_monotone ha c hAB) u 0).value (timeAffine a c s))
          (freeTest (timeAffine a c t-timeAffine a c s) (dualAffineTest ha b φ)) := by rw [integral_smul]
    _ = a^2 • ((a^2)⁻¹ • ∫ r in
        Icc (timeAffine a c A) (timeAffine a c B) ∩ Iio (timeAffine a c t),
        Lp.toTemperedDistribution
          ((criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0).value r)
          (freeTest (timeAffine a c t-r) (dualAffineTest ha b φ))) :=
      congrArg (fun z : ℂ => a^2 • z) (timeAffine_integral_past ha c A B t (fun r =>
        Lp.toTemperedDistribution
          ((criticalPathIntervalSource hDensity hSob hH (timeAffine_monotone ha c hAB) u 0).value r)
          (freeTest (timeAffine a c t-r) (dualAffineTest ha b φ))))
    _ = _ := by rw [smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 ha.ne'),one_smul]

#print axioms nonlinear_source_integrand_ae
#print axioms nonlinear_source_past_integral
end HartreeF.NonlinearAffine
