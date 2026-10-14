import FL1SourceRestriction
import FEndpointSourceWeakDerivative
import FEnergyCriticalTimeConsumer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal Topology
namespace HartreeF.RawStabilityInputs
open EnergySpace TimeHolder SobolevStretch StationarySelfTest
open ActualDuhamelPath IntervalTimeTransport Retarded CriticalPathRestriction
open CriticalTimeSobolev WeakHartreeProduct

abbrev SourceGradient := EuclideanSpace ℂ (Fin 3)
abbrev sourceExponent : ℝ≥0∞ := ENNReal.ofReal (6/5 : ℝ)
local instance : Fact (1 ≤ sourceExponent) := ⟨by norm_num⟩
local instance : Fact (sourceExponent ≠ ∞) := ⟨by norm_num⟩

/-- Explicit a.e. spatial Bochner weak-gradient meaning of the error norm.
The value is only locally time-L1; the one actual vector gradient is globally
time-L2 on I. No compatible source, mild equation or numerical W cap is input.
This definition does not assert a spacetime-distribution slicing theorem. -/
structure RawSpatialGradientSource (I : Set ℝ) (e : ℝ → Space → ℂ)
    (G : ℝ → Space → SourceGradient) : Prop where
  value_joint : AEStronglyMeasurable (fun z : ℝ × Space => e z.1 z.2)
    ((volume.restrict I).prod volume)
  gradient_joint : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2)
    ((volume.restrict I).prod volume)
  value_local : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I →
    mixedNorm (localMeasure a b) volume 1 sourceExponent e ≠ ∞
  gradient_finite : mixedNorm (volume.restrict I) volume 2 sourceExponent G ≠ ∞
  weak_gradient : ∀ᵐ t ∂volume.restrict I,
    HasWeakGradient (fun x => (e t x).re) (fun x => gradientReal (G t x)) ∧
    HasWeakGradient (fun x => (e t x).im) (fun x => gradientImag (G t x))

namespace RawSpatialGradientSource
variable {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (h : RawSpatialGradientSource I e G)

 theorem localMeasure_le {a b : ℝ} (hI : Icc a b ⊆ I) :
    localMeasure a b ≤ volume.restrict I := Measure.restrict_mono_set volume hI

include h

theorem value_local_joint {a b : ℝ} (hI : Icc a b ⊆ I) :
    AEStronglyMeasurable (fun z : ℝ × Space => e z.1 z.2)
      ((localMeasure a b).prod volume) :=
  h.value_joint.mono_measure (Measure.prod_mono (localMeasure_le hI) le_rfl)

theorem gradient_local_joint {a b : ℝ} (hI : Icc a b ⊆ I) :
    AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2)
      ((localMeasure a b).prod volume) :=
  h.gradient_joint.mono_measure (Measure.prod_mono (localMeasure_le hI) le_rfl)

theorem gradient_local_finite {a b : ℝ} (hI : Icc a b ⊆ I) :
    mixedNorm (localMeasure a b) volume 2 sourceExponent G ≠ ∞ :=
  ne_top_of_le_ne_top h.gradient_finite
    (eLpNorm_mono_measure _ (localMeasure_le hI))

theorem value_slices {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    ∀ᵐ t ∂localMeasure a b, MemLp (e t) sourceExponent volume :=
  finite_mixedNorm_ae_slice_memLp _ volume 1 sourceExponent (by norm_num) (by norm_num)
    e (h.value_local hab hI)

theorem gradient_slices {a b : ℝ} (hI : Icc a b ⊆ I) :
    ∀ᵐ t ∂localMeasure a b, MemLp (G t) sourceExponent volume :=
  finite_mixedNorm_ae_slice_memLp _ volume 2 sourceExponent (by norm_num) (by norm_num)
    G (h.gradient_local_finite hI)

def scalarClass {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    Lp SourceSpace 1 (localMeasure a b) :=
  jointLpRealization (localMeasure a b) volume 1 sourceExponent
    (fun z : ℝ × Space => e z.1 z.2) (h.value_local_joint hI)
    (h.value_slices hab hI) (h.value_local hab hI)

def vectorClass {a b : ℝ} (hI : Icc a b ⊆ I) :
    Lp (Lp SourceGradient sourceExponent (volume : Measure Space)) 2 (localMeasure a b) :=
  jointLpRealization (localMeasure a b) volume 2 sourceExponent
    (fun z : ℝ × Space => G z.1 z.2) (h.gradient_local_joint hI)
    (h.gradient_slices hI) (h.gradient_local_finite hI)

theorem scalarClass_ae {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    ∀ᵐ t ∂localMeasure a b, (h.scalarClass hab hI t : Space → ℂ) =ᵐ[volume] e t :=
  jointLpRealization_coeFn _ _ _ _ _ _ _ _

theorem vectorClass_ae {a b : ℝ} (hI : Icc a b ⊆ I) :
    ∀ᵐ t ∂localMeasure a b,
      (h.vectorClass hI t : Space → SourceGradient) =ᵐ[volume] G t :=
  jointLpRealization_coeFn _ _ _ _ _ _ _ _

theorem scalarClass_norm {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    ‖h.scalarClass hab hI‖ = (mixedNorm (localMeasure a b) volume 1 sourceExponent e).toReal :=
  jointLpRealization_norm _ _ _ _ _ _ _ _

theorem vectorClass_norm {a b : ℝ} (hI : Icc a b ⊆ I) :
    ‖h.vectorClass hI‖ = (mixedNorm (localMeasure a b) volume 2 sourceExponent G).toReal :=
  jointLpRealization_norm _ _ _ _ _ _ _ _

/-- Actual spatial weak derivatives produce all source compatibility fields. -/
def compactSource {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    CompatibleL1IntervalSource a b where
  value := h.scalarClass hab hI
  gradient := fun j => endpointGradientCoordinateSource (localMeasure a b) j (h.vectorClass hI)
  derivative := by
    have hc := ae_all_iff.mpr (fun j =>
      endpointGradientCoordinateSource_coeFn (localMeasure a b) j (h.vectorClass hI))
    filter_upwards [ae_mono (localMeasure_le hI) h.weak_gradient,
      h.scalarClass_ae hab hI, h.vectorClass_ae hI, hc] with t hw he hG hc
    intro j
    rw [hc j]
    apply endpointSource_weakDerivative_of_weakGradients _ _ (e t) he
    · exact weakGradient_congr_fields hw.1 Filter.EventuallyEq.rfl
        (hG.symm.mono fun x hx => congrArg gradientReal hx)
    · exact weakGradient_congr_fields hw.2 Filter.EventuallyEq.rfl
        (hG.symm.mono fun x hx => congrArg gradientImag hx)

theorem compactSource_value_ae {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    ∀ᵐ t ∂localMeasure a b,
      ((h.compactSource hab hI).value t : Space → ℂ) =ᵐ[volume] e t :=
  h.scalarClass_ae hab hI

theorem compactSource_gradient_ae {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I)
    (j : Fin 3) : ∀ᵐ t ∂localMeasure a b,
      ((h.compactSource hab hI).gradient j t : Space → ℂ) =ᵐ[volume]
        fun x => G t x j := by
  filter_upwards [endpointGradientCoordinateSource_coeFn (localMeasure a b) j
    (h.vectorClass hI), h.vectorClass_ae hI] with t ht hG
  change endpointGradientCoordinateSource (localMeasure a b) j (h.vectorClass hI) t =ᵐ[volume] _
  rw [ht]
  exact Filter.EventuallyEq.trans (endpointGradientCoordinate_coeFn j _)
    (hG.mono fun x hx => congrArg (fun v : SourceGradient => v j) hx)

/-- Reassembling the three scalar classes recovers the original vector G,
not merely another gradient with a numerical bound. -/
theorem compactSource_vector_ae {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    ∀ᵐ t ∂localMeasure a b,
      (fun x => (WithLp.toLp 2 (fun j : Fin 3 => (h.compactSource hab hI).gradient j t x) :
        SourceGradient)) =ᵐ[volume] G t := by
  filter_upwards [ae_all_iff.mpr (h.compactSource_gradient_ae hab hI)] with t ht
  filter_upwards [ae_all_iff.mpr ht] with x hx
  exact PiLp.ext fun j => hx j

/-- Projection to each component has operator bound one at both Lp levels. -/
theorem compactSource_gradient_component_norm_le {a b : ℝ}
    (hab : a ≤ b) (hI : Icc a b ⊆ I) (j : Fin 3) :
    ‖(h.compactSource hab hI).gradient j‖ ≤ ‖h.vectorClass hI‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [endpointGradientCoordinateSource_coeFn (localMeasure a b) j
    (h.vectorClass hI)] with t ht
  change ‖endpointGradientCoordinateSource (localMeasure a b) j (h.vectorClass hI) t‖ ≤ _
  rw [ht]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [endpointGradientCoordinate_coeFn j (h.vectorClass hI t)] with x hx
  rw [hx]
  exact PiLp.norm_apply_le _ j

theorem compactSource_gradient_norm_le {a b : ℝ}
    (hab : a ≤ b) (hI : Icc a b ⊆ I) :
    ‖(h.compactSource hab hI).gradient‖ ≤
      (mixedNorm (volume.restrict I) volume 2 sourceExponent G).toReal := by
  apply (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).mpr
  intro j
  apply (h.compactSource_gradient_component_norm_le hab hI j).trans
  rw [h.vectorClass_norm hI]
  exact ENNReal.toReal_mono h.gradient_finite (eLpNorm_mono_measure _ (localMeasure_le hI))

theorem compactSource_restrict {a b c d : ℝ}
    (hab : a ≤ b) (hI : Icc a b ⊆ I) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    (h.compactSource hab hI).restrict hac hdb =
      h.compactSource hcd ((Icc_subset_Icc hac hdb).trans hI) := by
  apply CompatibleL1IntervalSource.ext_value_gradient
  · apply Lp.ext
    filter_upwards [(h.compactSource hab hI).restrict_value_coeFn hac hdb,
      ae_mono (localMeasure_mono hac hdb) (h.compactSource_value_ae hab hI),
      h.compactSource_value_ae hcd ((Icc_subset_Icc hac hdb).trans hI)] with t ht h1 h2
    rw [ht]
    exact Lp.ext (h1.trans h2.symm)
  · funext j
    apply Lp.ext
    filter_upwards [(h.compactSource hab hI).restrict_gradient_coeFn hac hdb j,
      ae_mono (localMeasure_mono hac hdb) (h.compactSource_gradient_ae hab hI j),
      h.compactSource_gradient_ae hcd ((Icc_subset_Icc hac hdb).trans hI) j] with t ht h1 h2
    rw [ht]
    exact Lp.ext (h1.trans h2.symm)

end RawSpatialGradientSource
#print axioms RawSpatialGradientSource.compactSource
#print axioms RawSpatialGradientSource.compactSource_vector_ae
#print axioms RawSpatialGradientSource.compactSource_gradient_norm_le
#print axioms RawSpatialGradientSource.compactSource_restrict
end HartreeF.RawStabilityInputs
