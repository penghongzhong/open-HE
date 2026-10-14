import FActualPathGluing
import FEndpointHartreeDuhamelOutput

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.CriticalPathGluing
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalPathRestriction EndpointOutput

variable {a c b : ℝ}

/-- Glue the actual endpoint Bochner witnesses of the same joined energy path. -/
def gluePath_endpointWitness (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩)
    (Wu : EndpointGradientWitness (intervalMeasure a c) (energyPath _ u))
    (Wv : EndpointGradientWitness (intervalMeasure c b) (energyPath _ v)) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (gluePath hac hcb u v hm)) where
  field j := glueIntervalLp (E := Lp ℂ 6 (volume : Measure V)) 2 hac hcb (Wu.field j) (Wv.field j)
  agrees j := by
    have he : ∀ᵐ t ∂localMeasure a b,
        (gluedRepresentative (E := Lp ℂ 6 (volume : Measure V)) 2 hac hcb (Wu.field j) (Wv.field j) t : V → ℂ) =ᵐ[volume]
          energyGradient j (gluedEnergyPath hac hcb u v hm t) := by
      filter_upwards [ae_adjacent_intervals hac hcb
        ((Wu.toLocal hac).agrees j) ((Wv.toLocal hcb).agrees j)] with t ht
      by_cases hc : t ≤ c
      · have hE : gluedEnergyPath hac hcb u v hm t =
            extendEnergyPath hac (energyPath _ u) t := ite_eq_left hc
        have hW : gluedRepresentative (E := Lp ℂ 6 (volume : Measure V)) 2 hac hcb (Wu.field j) (Wv.field j) t =
            toLocalLp (E := Lp ℂ 6 (volume : Measure V)) hac 2 (Wu.field j) t := ite_eq_left hc
        simpa only [hE, hW, EndpointGradientWitness.toLocal, extendEnergyPath, ContinuousMap.coe_mk] using ht.1 hc
      · have hE : gluedEnergyPath hac hcb u v hm t =
            extendEnergyPath hcb (energyPath _ v) t := ite_eq_right hc
        have hW : gluedRepresentative (E := Lp ℂ 6 (volume : Measure V)) 2 hac hcb (Wu.field j) (Wv.field j) t =
            toLocalLp (E := Lp ℂ 6 (volume : Measure V)) hcb 2 (Wv.field j) t := ite_eq_right hc
        simpa only [hE, hW, EndpointGradientWitness.toLocal, extendEnergyPath, ContinuousMap.coe_mk] using ht.2 (lt_of_not_ge hc)
    have hi := (inclusion_measurePreserving a b).quasiMeasurePreserving.ae he
    filter_upwards [hi, glueIntervalLp_coeFn (E := Lp ℂ 6 (volume : Measure V)) 2 hac hcb (Wu.field j) (Wv.field j)]
      with t ht hw
    change (glueIntervalLp (E := Lp ℂ 6 (volume : Measure V)) 2 hac hcb (Wu.field j) (Wv.field j) t : V → ℂ) =ᵐ[volume]
      energyGradient j (gluedEnergyPath hac hcb u v hm (t : ℝ))
    rw [hw]
    exact ht

/-- Full endpoint membership survives actual adjacent-interval gluing. -/
theorem gluePath_fullZ (hac : a ≤ c) (hcb : c ≤ b)
    (u : CriticalPath (intervalMeasure a c)) (v : CriticalPath (intervalMeasure c b))
    (hm : energyPath _ u ⟨c, hac, le_rfl⟩ = energyPath _ v ⟨c, le_rfl, hcb⟩)
    (hu : FullZPath u) (hv : FullZPath v) : FullZPath (gluePath hac hcb u v hm) := by
  rcases hu with ⟨Wu⟩
  rcases hv with ⟨Wv⟩
  exact ⟨gluePath_endpointWitness hac hcb u v hm Wu Wv⟩

end HartreeF.CriticalPathGluing
