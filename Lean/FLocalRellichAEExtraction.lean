import FCutoffRellich
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalRellich
open EnergySpace SobolevStretch CutoffApproximation
attribute [local irreducible] energySubmodule
attribute [local instance 101] secondCountableTopologyEither_of_left

/-- One native increasing diagonal makes the growing-cutoff errors small. -/
theorem cutoff_diagonal_small (hRel : OrdinaryRellichBall)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {u : ℕ → EnergyState} {f : EnergyState} {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B)
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (u n)) v) atTop
        (𝓝 (inner ℝ (energyGradient j f) v))) :
    ∃ d : ℕ → ℕ, StrictMono d ∧
      Tendsto (fun n => cutoffValue n (u (d n)-f)) atTop (𝓝 (0 : L2)) := by
  have hex (k : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
      ‖cutoffValue k (u n-f)‖ < 1/((k:ℝ)+1) := by
    have ht : Tendsto (fun n => cutoffValue k (u n)-cutoffValue k f) atTop (𝓝 (0 : L2)) := by
      simpa only [sub_self] using (cutoffValue_tendsto hRel hSob k hB hweak).sub_const (cutoffValue k f)
    simpa only [map_sub, dist_zero_right] using
      Metric.tendsto_atTop.mp ht (1/((k:ℝ)+1)) (by positivity)
  choose N hN using hex
  let d : ℕ → ℕ := fun n => Nat.rec (N 0) (fun k prev => max (N (k+1)) (prev+1)) n
  have hdN (n : ℕ) : N n ≤ d n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  have hd : StrictMono d := strictMono_nat_of_lt_succ (fun n =>
    lt_of_lt_of_le (Nat.lt_succ_self (d n)) (le_max_right _ _))
  refine ⟨d,hd,tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hN n (d n) (hdN n)).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- The exact a.e. extraction needed by the one-profile Hartree split, produced
from the ordinary ball compactness and genuine gradient weak convergence.
No scalar L2, strong L6, or a.e. convergence assumption is imposed on the input. -/
theorem exists_ae_subsequence_of_gradient_weak (hRel : OrdinaryRellichBall)
    {K : ℝ} (hSob : OrdinarySobolev K)
    {u : ℕ → EnergyState} {f : EnergyState} {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B)
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (u n)) v) atTop
        (𝓝 (inner ℝ (energyGradient j f) v))) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ x ∂volume, Tendsto (fun n => energyValue (u (σ n)) x) atTop (𝓝 (energyValue f x)) := by
  obtain ⟨d,hd,ht⟩ := cutoff_diagonal_small hRel hSob hB hweak
  obtain ⟨η,hη,hηae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have he (n : ℕ) : (cutoffValue n (u (d n)-f) : Space → ℂ) =ᵐ[volume]
      fun x => cutoff n x • (energyValue (u (d n)) x-energyValue f x) := by
    filter_upwards [cutoffValue_ae n (u (d n)-f), Lp.coeFn_sub (energyValue (u (d n))) (energyValue f)]
      with x hx hs
    rw [hx, map_sub, hs, Pi.sub_apply]
  refine ⟨d ∘ η,hd.comp hη,?_⟩
  filter_upwards [hηae, ae_all_iff.mpr he, Lp.coeFn_zero ℂ 2 (volume : Measure Space)]
    with x hx hxe hz
  rw [hz] at hx
  have hevent : (fun n => cutoffValue (η n) (u (d (η n))-f) x) =ᶠ[atTop]
      (fun n => energyValue (u (d (η n))) x-energyValue f x) := by
    filter_upwards [hη.tendsto_atTop.eventually (cutoff_eventually_one x)] with n hn
    rw [hxe, hn, one_smul]
  have hlim := (hx.congr' hevent).add_const (energyValue f x)
  simpa only [Pi.zero_apply, zero_add, sub_add_cancel, Function.comp_apply] using hlim

#print axioms cutoff_diagonal_small
#print axioms exists_ae_subsequence_of_gradient_weak
end HartreeF.LocalRellich
