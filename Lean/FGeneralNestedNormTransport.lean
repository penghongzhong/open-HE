import FGeneralRepresentativeTransport

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation

/-- Nested a.e. equality alone transports every scalar or vector mixed norm. -/
theorem mixedNorm_congr_nested_ae {T X E : Type*} [MeasurableSpace T] [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure T) (ν : Measure X) (p q : ℝ≥0∞)
    {f g : T → X → E} (h : ∀ᵐ t ∂μ, f t =ᵐ[ν] g t) :
    mixedNorm μ ν p q f = mixedNorm μ ν p q g := by
  apply eLpNorm_congr_ae
  exact h.mono fun _ ht => eLpNorm_congr_ae ht

/-- Finite coordinate equality reconstructs the actual complex Euclidean vector a.e. -/
theorem packedGradient_congr_nested_ae {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) {F G : T → X → CGradient}
    (h : ∀ j : Fin 3, ∀ᵐ t ∂μ, (fun x => F t x j) =ᵐ[ν] (fun x => G t x j)) :
    ∀ᵐ t ∂μ, F t =ᵐ[ν] G t := by
  filter_upwards [eventually_all.mpr h] with t ht
  filter_upwards [eventually_all.mpr ht] with x hx
  ext j
  exact hx j

theorem packedGradient_mixedNorm_congr_nested_ae
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) (p q : ℝ≥0∞) {F G : T → X → CGradient}
    (h : ∀ j : Fin 3, ∀ᵐ t ∂μ, (fun x => F t x j) =ᵐ[ν] (fun x => G t x j)) :
    mixedNorm μ ν p q F = mixedNorm μ ν p q G :=
  mixedNorm_congr_nested_ae μ ν p q (packedGradient_congr_nested_ae μ ν h)

#print axioms mixedNorm_congr_nested_ae
#print axioms packedGradient_congr_nested_ae
#print axioms packedGradient_mixedNorm_congr_nested_ae
end HartreeF.GeneralProfileCross
