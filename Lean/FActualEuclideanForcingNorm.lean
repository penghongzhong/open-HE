import FEssentialEnergyCap
import FCompatibleL1IntervalSource

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualDuhamelPath.CompatibleL1IntervalSource
open EnergySpace Retarded TimeHolder IntervalTimeTransport

/-- The complex Euclidean vector made from the actual three distributional
spatial derivative coordinates of the original scalar L1 source. -/
def complexGradient {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (t : ℝ) (x : Space) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j => E.gradient j t x)

@[simp] theorem complexGradient_coordinate {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (t : ℝ) (x : Space) (j : Fin 3) :
    E.complexGradient t x j = E.gradient j t x := rfl

/-- The paper forcing norm of that same actual vector field. -/
def paperForcingSize {a b : ℝ} (E : CompatibleL1IntervalSource a b) : ℝ≥0∞ :=
  mixedNorm (localMeasure a b) volume 2 (ENNReal.ofReal (6/5 : ℝ)) E.complexGradient

theorem gradient_coordinate_mixedNorm_eq {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (j : Fin 3) :
    mixedNorm (localMeasure a b) volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t x => E.gradient j t x) = ‖E.gradient j‖ₑ := by
  unfold mixedNorm
  calc
    _ = eLpNorm (fun t => ‖E.gradient j t‖ₑ) 2 (localMeasure a b) := by
      apply eLpNorm_congr_ae
      filter_upwards [] with t
      exact (Lp.enorm_def _).symm
    _ = eLpNorm (E.gradient j) 2 (localMeasure a b) :=
      eLpNorm_enorm _ (Lp.aestronglyMeasurable _)
    _ = _ := (Lp.enorm_def _).symm

theorem gradient_coordinate_profile_memLp {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (j : Fin 3) :
    MemLp (fun t => eLpNorm (E.gradient j t) (ENNReal.ofReal (6/5 : ℝ)) volume)
      2 (localMeasure a b) := by
  have he : (fun t => eLpNorm (E.gradient j t) (ENNReal.ofReal (6/5 : ℝ)) volume) =ᵐ[localMeasure a b]
      (fun t => ‖E.gradient j t‖ₑ) := by
    filter_upwards [] with t
    exact (Lp.enorm_def _).symm
  exact (memLp_congr_ae he).mpr (Lp.memLp (E.gradient j)).enorm

/-- Projection onto any actual complex coordinate has operator bound one.
No dimension factor or smallness threshold is lost in this input direction. -/
theorem gradient_coordinate_le_paperForcingSize {a b : ℝ}
    (E : CompatibleL1IntervalSource a b) (j : Fin 3) :
    ENNReal.ofReal ‖E.gradient j‖ ≤ E.paperForcingSize := by
  apply ((ofReal_norm _).trans (E.gradient_coordinate_mixedNorm_eq j).symm).le.trans
  unfold paperForcingSize mixedNorm
  apply eLpNorm_mono_enorm_ae (E.gradient_coordinate_profile_memLp j).aestronglyMeasurable
  filter_upwards [] with t
  simp only [enorm_eq_self]
  apply eLpNorm_mono (Lp.aestronglyMeasurable _)
  intro x
  rw [← E.complexGradient_coordinate t x j]
  exact PiLp.norm_apply_le _ j

theorem gradient_norm_le_of_paperForcingSize {a b N : ℝ}
    (E : CompatibleL1IntervalSource a b) (hN : 0 ≤ N)
    (h : E.paperForcingSize ≤ ENNReal.ofReal N) : ‖E.gradient‖ ≤ N := by
  apply (pi_norm_le_iff_of_nonneg hN).mpr
  intro j
  exact (ENNReal.ofReal_le_ofReal_iff hN).mp
    ((E.gradient_coordinate_le_paperForcingSize j).trans h)

end HartreeF.ActualDuhamelPath.CompatibleL1IntervalSource

namespace HartreeF.PaperNormCompactPerturbation
open EnergySpace CriticalPathSpace CriticalSourceBounds CriticalJointSources TimeHolder
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath jointFields

/-- The existing jointly measurable S representative is the same actual
energy value on almost every time/space slice. -/
theorem pathValueSize_eq_actual_S {a b : ℝ} (q : CriticalPath (intervalMeasure a b)) :
    pathValueSize (intervalMeasure a b) q =
      mixedNorm (intervalMeasure a b) volume 10 10 (fun t => energyValue (energyPath _ q t)) := by
  unfold pathValueSize mixedNorm
  apply eLpNorm_congr_ae
  filter_upwards [(jointFields _ q).slice_eq] with t ht
  exact eLpNorm_congr_ae ht.1

end HartreeF.PaperNormCompactPerturbation
