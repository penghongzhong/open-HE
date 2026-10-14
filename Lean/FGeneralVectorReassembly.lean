import FGradientMixedTriangle
import FProfileCutoffGradient
import FCompactCrossTerms

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation CompactCross

/-- Literal extended L2-time, L(6/5)-space norm of a complex Euclidean vector field. -/
def vectorForcingNorm (G : ℝ → Space → CGradient) : ℝ≥0∞ :=
  mixedNorm volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) G

/-- Exact reconstruction in the Euclidean space, without an assertion about norm equality. -/
theorem packGradient_coordinates (v : CGradient) :
    packGradient (v 0) (v 1) (v 2) = v := by
  ext j
  rw [packGradient_coordinate]
  fin_cases j <;> rfl

/-- The actual vector forcing norm is bounded by the sum of its three coordinate norms. -/
theorem vectorForcingNorm_le_sum (G : ℝ → Space → CGradient)
    (hG : ∀ j : Fin 3, AEStronglyMeasurable
      (fun z : ℝ × Space => G z.1 z.2 j) (volume.prod volume)) :
    vectorForcingNorm G ≤ ∑ j : Fin 3, forcingNorm (fun t x => G t x j) := by
  have hb := pack_mixed_norm_le volume
    (fun j t x => G t x j) (fun j t x => G t x j) hG
    (fun _ => Filter.Eventually.of_forall fun _ => Filter.EventuallyEq.rfl)
  simpa only [vectorForcingNorm, forcingNorm, packGradient_coordinates,
    Fin.sum_univ_three, add_assoc] using hb

/-- Joint measurability of the vector is sufficient for the finite-dimensional bound. -/
theorem vectorForcingNorm_le_sum_of_joint (G : ℝ → Space → CGradient)
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) (volume.prod volume)) :
    vectorForcingNorm G ≤ ∑ j : Fin 3, forcingNorm (fun t x => G t x j) := by
  apply vectorForcingNorm_le_sum
  intro j
  exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp_aestronglyMeasurable hG

/-- Coordinate vanishing transfers along the same arbitrary original filter. -/
theorem vectorForcingNorm_tendsto_zero_of_coordinates {ι : Type*} {l : Filter ι}
    (G : ι → ℝ → Space → CGradient)
    (hG : ∀ i, ∀ j : Fin 3, AEStronglyMeasurable
      (fun z : ℝ × Space => G i z.1 z.2 j) (volume.prod volume))
    (hlim : ∀ j : Fin 3, Tendsto
      (fun i => forcingNorm (fun t x => G i t x j)) l (𝓝 0)) :
    Tendsto (fun i => vectorForcingNorm (G i)) l (𝓝 0) := by
  have hsum : Tendsto
      (fun i => ∑ j : Fin 3, forcingNorm (fun t x => G i t x j)) l (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ => hlim j)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun i => vectorForcingNorm_le_sum (G i) (hG i))

/-- A directly usable form for jointly measurable vector sequences or nets. -/
theorem vectorForcingNorm_tendsto_zero_of_joint {ι : Type*} {l : Filter ι}
    (G : ι → ℝ → Space → CGradient)
    (hG : ∀ i, AEStronglyMeasurable
      (fun z : ℝ × Space => G i z.1 z.2) (volume.prod volume))
    (hlim : ∀ j : Fin 3, Tendsto
      (fun i => forcingNorm (fun t x => G i t x j)) l (𝓝 0)) :
    Tendsto (fun i => vectorForcingNorm (G i)) l (𝓝 0) := by
  apply vectorForcingNorm_tendsto_zero_of_coordinates G _ hlim
  intro i j
  exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) j).comp_aestronglyMeasurable (hG i)

#print axioms packGradient_coordinates
#print axioms vectorForcingNorm_le_sum
#print axioms vectorForcingNorm_le_sum_of_joint
#print axioms vectorForcingNorm_tendsto_zero_of_coordinates
#print axioms vectorForcingNorm_tendsto_zero_of_joint
end HartreeF.GeneralProfileCross
