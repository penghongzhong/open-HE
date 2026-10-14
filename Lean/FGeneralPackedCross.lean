import FGeneralVectorReassembly
import FCrossContinuityTime

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation CompactCross CrossContinuity

/-- The inner pure cross derivative with all three actual complex coordinates retained. -/
def packedInnerCross (α c : ℝ) (u : ℝ → Space → ℂ)
    (H : ℝ → Space → CGradient) (v : ℝ → Space → ℂ) : ℝ → Space → CGradient :=
  fun t x => packGradient
    (innerCross α c u (fun s y => H s y 0) v t x)
    (innerCross α c u (fun s y => H s y 1) v t x)
    (innerCross α c u (fun s y => H s y 2) v t x)

/-- The outer pure cross derivative with all three actual complex coordinates retained. -/
def packedOuterCross (α c : ℝ) (u v : ℝ → Space → ℂ)
    (K : ℝ → Space → CGradient) : ℝ → Space → CGradient :=
  fun t x => packGradient
    (outerCross α c u v (fun s y => K s y 0) t x)
    (outerCross α c u v (fun s y => K s y 1) t x)
    (outerCross α c u v (fun s y => K s y 2) t x)

theorem packedInnerCross_coordinate (α c : ℝ) (u : ℝ → Space → ℂ)
    (H : ℝ → Space → CGradient) (v : ℝ → Space → ℂ) (j : Fin 3) :
    (fun t x => packedInnerCross α c u H v t x j) =
      innerCross α c u (fun t x => H t x j) v := by
  funext t x
  unfold packedInnerCross
  rw [packGradient_coordinate]
  fin_cases j <;> rfl

theorem packedOuterCross_coordinate (α c : ℝ) (u v : ℝ → Space → ℂ)
    (K : ℝ → Space → CGradient) (j : Fin 3) :
    (fun t x => packedOuterCross α c u v K t x j) =
      outerCross α c u v (fun t x => K t x j) := by
  funext t x
  unfold packedOuterCross
  rw [packGradient_coordinate]
  fin_cases j <;> rfl

theorem packedInnerCross_joint_measurable (α c : ℝ) {u v : ℝ → Space → ℂ}
    {H : ℝ → Space → CGradient}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => packedInnerCross α c u H v z.1 z.2)
      (volume.prod volume) := by
  have hc (j : Fin 3) := inner_joint_measurable α c (h := fun t x => H t x j) hu
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp_aestronglyMeasurable hH) hv
  exact (((hc 0).smul_const _).add ((hc 1).smul_const _)).add ((hc 2).smul_const _)

theorem packedOuterCross_joint_measurable (α c : ℝ) {u v : ℝ → Space → ℂ}
    {K : ℝ → Space → CGradient}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume))
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) (volume.prod volume)) :
    AEStronglyMeasurable (fun z : ℝ × Space => packedOuterCross α c u v K z.1 z.2)
      (volume.prod volume) := by
  have hc (j : Fin 3) := outer_joint_measurable α c (k := fun t x => K t x j) hu hv
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp_aestronglyMeasurable hK)
  exact (((hc 0).smul_const _).add ((hc 1).smul_const _)).add ((hc 2).smul_const _)

theorem packedInnerCross_forcing_le_sum (α c : ℝ) {u v : ℝ → Space → ℂ}
    {H : ℝ → Space → CGradient}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume)) :
    vectorForcingNorm (packedInnerCross α c u H v) ≤
      ∑ j : Fin 3, forcingNorm (innerCross α c u (fun t x => H t x j) v) := by
  simpa only [packedInnerCross_coordinate] using vectorForcingNorm_le_sum_of_joint
    (packedInnerCross α c u H v) (packedInnerCross_joint_measurable α c hu hH hv)

theorem packedOuterCross_forcing_le_sum (α c : ℝ) {u v : ℝ → Space → ℂ}
    {K : ℝ → Space → CGradient}
    (hu : AEStronglyMeasurable (fun z : ℝ × Space => u z.1 z.2) (volume.prod volume))
    (hv : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) (volume.prod volume))
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) (volume.prod volume)) :
    vectorForcingNorm (packedOuterCross α c u v K) ≤
      ∑ j : Fin 3, forcingNorm (outerCross α c u v (fun t x => K t x j)) := by
  simpa only [packedOuterCross_coordinate] using vectorForcingNorm_le_sum_of_joint
    (packedOuterCross α c u v K) (packedOuterCross_joint_measurable α c hu hv hK)

/-- The same-filter transfer requires only coordinate cross decay and genuine input measurability. -/
theorem packedInnerCross_tendsto_zero {ι : Type*} {l : Filter ι} (α c : ℝ)
    (u v : ι → ℝ → Space → ℂ) (H : ι → ℝ → Space → CGradient)
    (hu : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => u i z.1 z.2) (volume.prod volume))
    (hH : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => H i z.1 z.2) (volume.prod volume))
    (hv : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => v i z.1 z.2) (volume.prod volume))
    (hlim : ∀ j : Fin 3, Tendsto
      (fun i => forcingNorm (innerCross α c (u i) (fun t x => H i t x j) (v i))) l (𝓝 0)) :
    Tendsto (fun i => vectorForcingNorm (packedInnerCross α c (u i) (H i) (v i))) l (𝓝 0) := by
  apply vectorForcingNorm_tendsto_zero_of_joint
    (fun i => packedInnerCross α c (u i) (H i) (v i))
    (fun i => packedInnerCross_joint_measurable α c (hu i) (hH i) (hv i))
  simpa only [packedInnerCross_coordinate] using hlim

theorem packedOuterCross_tendsto_zero {ι : Type*} {l : Filter ι} (α c : ℝ)
    (u v : ι → ℝ → Space → ℂ) (K : ι → ℝ → Space → CGradient)
    (hu : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => u i z.1 z.2) (volume.prod volume))
    (hv : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => v i z.1 z.2) (volume.prod volume))
    (hK : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => K i z.1 z.2) (volume.prod volume))
    (hlim : ∀ j : Fin 3, Tendsto
      (fun i => forcingNorm (outerCross α c (u i) (v i) (fun t x => K i t x j))) l (𝓝 0)) :
    Tendsto (fun i => vectorForcingNorm (packedOuterCross α c (u i) (v i) (K i))) l (𝓝 0) := by
  apply vectorForcingNorm_tendsto_zero_of_joint
    (fun i => packedOuterCross α c (u i) (v i) (K i))
    (fun i => packedOuterCross_joint_measurable α c (hu i) (hv i) (hK i))
  simpa only [packedOuterCross_coordinate] using hlim

#print axioms packedInnerCross_coordinate
#print axioms packedOuterCross_coordinate
#print axioms packedInnerCross_joint_measurable
#print axioms packedOuterCross_joint_measurable
#print axioms packedInnerCross_forcing_le_sum
#print axioms packedOuterCross_forcing_le_sum
#print axioms packedInnerCross_tendsto_zero
#print axioms packedOuterCross_tendsto_zero
end HartreeF.GeneralProfileCross
