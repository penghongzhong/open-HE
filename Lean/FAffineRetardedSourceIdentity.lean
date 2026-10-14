import FAffineDistributionPairing
import FAffineRetardedTimeChange
import FAffineIntervalEnergyPath
import FParabolicCompatibleL1Source

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Set Filter
open scoped ENNReal
namespace HartreeF.AffinePath
open EnergySpace TimeHolder CriticalAffine AffineMixed AffineL1Source
open RawStabilityInputs ActualDuhamelPath IntervalTimeTransport Retarded FreeFlow

variable {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
  (hRaw : RawSpatialGradientSource I e G) {a : ℝ} (ha : 0<a) (b : Space)
  (c A B : ℝ) (hAB : A≤B) (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆ I)

/-- Both scalar classes are the produced L1 classes of the SAME original e.
The dual free test and the a^2 source factor are derived, not assumed. -/
theorem parabolicCompactSource_integrand_ae (t : ℝ) (φ : FreeFlow.Test) :
    ∀ᵐ s ∂localMeasure A B,
      Lp.toTemperedDistribution ((parabolicCompactSource hRaw ha b c A B hAB hI).value s)
        (freeTest (t-s) φ)=
      a^2 • Lp.toTemperedDistribution
        ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).value (timeAffine a c s))
        (freeTest (timeAffine a c t-timeAffine a c s) (dualAffineTest ha b φ)) := by
  have hE := (timeAffine_quasiMeasurePreserving ha c
    (Icc (timeAffine a c A) (timeAffine a c B))).ae
    (hRaw.compactSource_value_ae (timeAffine_monotone ha c hAB) hI)
  rw [timeAffine_preimage_Icc ha c A B] at hE
  filter_upwards [hE,parabolicCompactSource_value_ae hRaw ha b c A B hAB hI] with s hsE hsF
  have hsE' : ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).value
      (timeAffine a c s) : Space → ℂ) =ᵐ[volume] e (timeAffine a c s) := hsE
  have hsF' : ((parabolicCompactSource hRaw ha b c A B hAB hI).value s : Space → ℂ) =ᵐ[volume]
      parabolicField a b c (5/2) e s := hsF
  have htime : timeAffine a c t-timeAffine a c s=a^2*(t-s) := by unfold timeAffine; ring
  simp only [Lp.toTemperedDistribution_apply,smul_eq_mul]
  rw [htime]
  calc
    _ = ∫ x, freeTest (t-s) φ x*parabolicField a b c (5/2) e s x := by
      apply integral_congr_ae
      exact hsF'.mono (fun x hx => congrArg (fun z : ℂ => freeTest (t-s) φ x*z) hx)
    _ = a^2 • ∫ y, dualAffineTest ha b (freeTest (t-s) φ) y*e (timeAffine a c s) y :=
      parabolicSource_spatial_pairing ha b c e s (freeTest (t-s) φ)
    _ = a^2 • ∫ y, freeTest (a^2*(t-s)) (dualAffineTest ha b φ) y*e (timeAffine a c s) y := by
      rw [dualAffineTest_freeTest]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact hsE'.symm.mono (fun y hy => congrArg
        (fun z : ℂ => freeTest (a^2*(t-s)) (dualAffineTest ha b φ) y*z) hy)

/-- The exact past integral of the transformed scalar-L1 source equals the
original past integral with the dual affine test. -/
theorem parabolicCompactSource_past_integral (t : ℝ) (φ : FreeFlow.Test) :
    (∫ s in Icc A B ∩ Iio t,
      Lp.toTemperedDistribution ((parabolicCompactSource hRaw ha b c A B hAB hI).value s)
        (freeTest (t-s) φ))=
    ∫ r in Icc (timeAffine a c A) (timeAffine a c B) ∩ Iio (timeAffine a c t),
      Lp.toTemperedDistribution ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).value r)
        (freeTest (timeAffine a c t-r) (dualAffineTest ha b φ)) := by
  have he := ae_mono (Measure.restrict_mono_set volume
    (show Icc A B ∩ Iio t ⊆ Icc A B from inter_subset_left))
    (parabolicCompactSource_integrand_ae hRaw ha b c A B hAB hI t φ)
  calc
    _ = ∫ s in Icc A B ∩ Iio t,
        a^2 • Lp.toTemperedDistribution
          ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).value (timeAffine a c s))
          (freeTest (timeAffine a c t-timeAffine a c s) (dualAffineTest ha b φ)) :=
      integral_congr_ae he
    _ = a^2 • ∫ s in Icc A B ∩ Iio t,
        Lp.toTemperedDistribution
          ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).value (timeAffine a c s))
          (freeTest (timeAffine a c t-timeAffine a c s) (dualAffineTest ha b φ)) := by rw [integral_smul]
    _ = a^2 • ((a^2)⁻¹ • ∫ r in
        Icc (timeAffine a c A) (timeAffine a c B) ∩ Iio (timeAffine a c t),
        Lp.toTemperedDistribution ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).value r)
          (freeTest (timeAffine a c t-r) (dualAffineTest ha b φ))) := by
      exact congrArg (fun z : ℂ => a^2 • z)
        (timeAffine_integral_past ha c A B t (fun r =>
          Lp.toTemperedDistribution
            ((hRaw.compactSource (timeAffine_monotone ha c hAB) hI).value r)
            (freeTest (timeAffine a c t-r) (dualAffineTest ha b φ))))
    _ = _ := by rw [smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 ha.ne'),one_smul]

#print axioms parabolicCompactSource_integrand_ae
#print axioms parabolicCompactSource_past_integral
end HartreeF.AffinePath
