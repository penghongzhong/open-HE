import FL2PartitionAssembly
import FPartitionPrefixGeometry
import FEndpointComplexVectorDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace HartreeF.FinitePerturbation
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalPathGluing
open ActualDuhamelPath ActualPathPartitions TimePartition EndpointOutput IntervalTimeTransport TimeHolder
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyGradient criticalGradient restrictPath

/-- Restrict the same genuine endpoint field together with its actual energy path. -/
def restrictEndpointWitness {a b c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (p : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ p)) :
    EndpointGradientWitness (intervalMeasure c d) (energyPath _ (restrictPath hac hcd hdb p)) where
  field j := restrictIntervalLp 2 hac hcd hdb (W.field j)
  agrees j := by
    filter_upwards [restrictIntervalLp_coeFn 2 hac hcd hdb (W.field j),
      ae_intervalInclusion hac hcd hdb (W.agrees j)] with t ht hw
    have he : energyPath _ (restrictPath hac hcd hdb p) t =
        energyPath _ p (intervalInclusion hac hdb t) := restrictPath_energy hac hcd hdb p t
    have hfield : (restrictIntervalLp 2 hac hcd hdb (W.field j) t : Space → ℂ) =ᵐ[volume]
        (W.field j (intervalInclusion hac hdb t) : Space → ℂ) :=
      Eventually.of_forall fun x => congrArg (fun z : Lp ℂ 6 (volume : Measure Space) => z x) ht
    have hgrad : (energyGradient j (energyPath _ p (intervalInclusion hac hdb t)) : Space → ℂ) =ᵐ[volume]
        energyGradient j (energyPath _ (restrictPath hac hcd hdb p) t) :=
      Eventually.of_forall fun x => congrArg (fun z : EnergyState => energyGradient j z x) he.symm
    exact hfield.trans (hw.trans hgrad)

/-- Every actual coordinate endpoint norm is bounded by the actual Euclidean norm. -/
theorem coordinate_endpoint_le_complex {a b : ℝ} (p : CriticalPath (intervalMeasure a b))
    (W : EndpointGradientWitness (intervalMeasure a b) (energyPath _ p)) (j : Fin 3) :
    mixedNorm (intervalMeasure a b) volume 2 6 (fun t => energyGradient j (energyPath _ p t)) ≤
      mixedNorm (intervalMeasure a b) volume 2 6 (fun t => energyComplexGradient (energyPath _ p t)) := by
  have hs (t : Set.Icc a b) : eLpNorm (energyGradient j (energyPath _ p t)) 6 volume ≤
      eLpNorm (energyComplexGradient (energyPath _ p t)) 6 volume := by
    apply eLpNorm_mono (Lp.aestronglyMeasurable _)
    intro x
    rw [← energyComplexGradient_coordinate]
    exact PiLp.norm_apply_le _ j
  exact eLpNorm_mono_enorm_ae (W.norm_profile_memLp j).aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa only [enorm_eq_self] using hs t)

/-- Actual per-piece Euclidean endpoint bounds control the whole endpoint norm.
The additional finite-coordinate assembly constant remains explicit. -/
theorem global_endpoint_le_piece_bound {a b H : ℝ} (hab : a ≤ b) (P : Partition a b)
    (p : CriticalPath (intervalMeasure a b)) (hZ : FullZPath p) (hH : 0 ≤ H)
    (hpieces : ∀ i : Fin P.count,
      mixedNorm (intervalMeasure (P.time i.castSucc) (P.time i.succ)) volume 2 6
        (fun t => energyComplexGradient (energyPath _ (piecePath P p i) t)) ≤ ENNReal.ofReal H) :
    mixedNorm (intervalMeasure a b) volume 2 6 (fun t => energyComplexGradient (energyPath _ p t)) ≤
      ENNReal.ofReal (3*(P.count : ℝ)*H) := by
  let W := Classical.choice hZ
  have hc (j : Fin 3) : mixedNorm (intervalMeasure a b) volume 2 6
      (fun t => energyGradient j (energyPath _ p t)) ≤ ENNReal.ofReal ((P.count : ℝ)*H) := by
    let f := toLocalLp hab 2 (W.field j)
    have hp (i : Fin P.count) : lpNorm f 2 (localMeasure (P.time i.castSucc) (P.time i.succ)) ≤ H := by
      let V := restrictEndpointWitness (P.mem_interval i.castSucc).1 (piece_order P i)
        (P.mem_interval i.succ).2 p W
      have he := (coordinate_endpoint_le_complex (piecePath P p i) V j).trans (hpieces i)
      unfold piecePath at he
      rw [V.mixedNorm_eq j] at he
      have hn : ‖V.field j‖ ≤ H := (ENNReal.ofReal_le_ofReal_iff hH).mp
        (by simpa only [ofReal_norm] using he)
      have hnorm : ‖V.field j‖ = lpNorm f 2 (localMeasure (P.time i.castSucc) (P.time i.succ)) :=
        restrictIntervalLp_norm_eq_lpNorm 2 (P.mem_interval i.castSucc).1 (piece_order P i)
          (P.mem_interval i.succ).2 (W.field j)
      exact hnorm.symm.le.trans hn
    have hb := lpNorm_two_le_count_mul_piece_bound hab P (Lp.memLp f) hH hp
    have hn : lpNorm f 2 (localMeasure a b) = ‖W.field j‖ :=
      (Lp.norm_def f).symm.trans (toLocalLp_norm hab 2 (W.field j))
    rw [W.mixedNorm_eq j, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hn.symm.le.trans hb)
  apply (criticalPath_complex_endpoint_le_sum p).trans
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hc j)
  apply hs.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  rw [← ENNReal.ofReal_ofNat (n:=3), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

end HartreeF.FinitePerturbation
