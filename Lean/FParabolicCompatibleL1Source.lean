import FRawAffineL1Source

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set Filter LineDeriv
open scoped ENNReal
namespace HartreeF.AffineL1Source
open AffineMixed RawStabilityInputs TimeHolder ActualDuhamelPath IntervalTimeTransport
open EnergySpace Retarded CriticalPathSpace

theorem timeAffine_interval_subset {a : ℝ} (ha : 0<a) (c A B : ℝ)
    {I : Set ℝ} (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆ I) :
    Icc A B ⊆ (timeAffine a c) ⁻¹' I := by
  rw [← timeAffine_preimage_Icc ha c A B]
  exact preimage_mono hI

/-- The accepted actual weak-gradient producer builds the target L1 bundle. -/
def parabolicCompactSource {I : Set ℝ} {e : ℝ → Space → ℂ}
    {G : ℝ → Space → SourceGradient} (h : RawSpatialGradientSource I e G)
    {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
    (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆ I) :
    CompatibleL1IntervalSource A B :=
  (rawSource_parabolic h ha b c).compactSource hAB (timeAffine_interval_subset ha c A B hI)

variable {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
  (h : RawSpatialGradientSource I e G) {a : ℝ} (ha : 0<a) (b : Space)
  (c A B : ℝ) (hAB : A≤B) (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆ I)

theorem parabolicCompactSource_value_ae : ∀ᵐ t ∂localMeasure A B,
    ((parabolicCompactSource h ha b c A B hAB hI).value t : Space → ℂ) =ᵐ[volume]
      parabolicField a b c (5/2) e t :=
  (rawSource_parabolic h ha b c).compactSource_value_ae hAB (timeAffine_interval_subset ha c A B hI)

theorem parabolicCompactSource_vector_ae : ∀ᵐ t ∂localMeasure A B,
    (fun x => (WithLp.toLp 2 (fun j : Fin 3 =>
      (parabolicCompactSource h ha b c A B hAB hI).gradient j t x) : SourceGradient)) =ᵐ[volume]
      parabolicField a b c (7/2) G t :=
  (rawSource_parabolic h ha b c).compactSource_vector_ae hAB (timeAffine_interval_subset ha c A B hI)

theorem parabolicCompactSource_derivative : ∀ᵐ t ∂localMeasure A B, ∀ j : Fin 3,
    ∂_{coordinate j} (Lp.toTemperedDistribution ((parabolicCompactSource h ha b c A B hAB hI).value t))=
      Lp.toTemperedDistribution ((parabolicCompactSource h ha b c A B hAB hI).gradient j t) :=
  (parabolicCompactSource h ha b c A B hAB hI).derivative

/-- Exact scalar-L1 class norm, with its non-invariant a^(-2) factor. -/
theorem parabolicCompactSource_value_norm :
    ‖(parabolicCompactSource h ha b c A B hAB hI).value‖=
      a^(-2:ℝ)*(mixedNorm (localMeasure (timeAffine a c A) (timeAffine a c B))
        volume 1 sourceExponent e).toReal := by
  change ‖(rawSource_parabolic h ha b c).scalarClass hAB (timeAffine_interval_subset ha c A B hI)‖=_
  rw [RawSpatialGradientSource.scalarClass_norm,
    (raw_source_local_scaled_norms h ha b c A B hAB hI).1,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _)]

/-- The bundle's component norm is bounded by the SAME original vector N. -/
theorem parabolicCompactSource_gradient_norm_le :
    ‖(parabolicCompactSource h ha b c A B hAB hI).gradient‖≤
      (mixedNorm (volume.restrict I) volume 2 sourceExponent G).toReal := by
  have hn := (rawSource_parabolic h ha b c).compactSource_gradient_norm_le
    hAB (timeAffine_interval_subset ha c A B hI)
  rw [parabolic_N_invariant ha b c I G h.gradient_joint] at hn
  exact hn

/-- Scalar L1 values determine their actual compatible weak derivative classes.
This is the value-only extensionality needed by later retarded consumers. -/
theorem compatibleL1_ext_value {A B : ℝ} (F H : CompatibleL1IntervalSource A B)
    (hv : F.value=H.value) : F=H := by
  have hg : F.gradient=H.gradient := by
    funext j
    apply Lp.ext
    filter_upwards [F.derivative,H.derivative] with t hF hH
    exact Lp.ext (spatial_ae_eq_of_distribution_eq _ _
      ((hF j).symm.trans (by simpa only [hv] using hH j)))
  exact CompatibleL1IntervalSource.ext_value_gradient hv hg

#print axioms timeAffine_interval_subset
#print axioms parabolicCompactSource
#print axioms parabolicCompactSource_value_ae
#print axioms parabolicCompactSource_vector_ae
#print axioms parabolicCompactSource_derivative
#print axioms parabolicCompactSource_value_norm
#print axioms parabolicCompactSource_gradient_norm_le
#print axioms compatibleL1_ext_value
end HartreeF.AffineL1Source
