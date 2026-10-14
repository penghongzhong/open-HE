import FActualFreePathDifference
import FBackwardFreePathCaps
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-! The actual compact homogeneous carrier has one uniform small free time window.
AUTHOR CANDIDATE; NOT COMPILED. No uniform lifespan is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology
namespace HartreeF.CompactUniformLifespan
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest ActualStrichartz TimeHolder FreeDataDependence
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient freeCriticalPath freeEnergyState
  criticalPathOfGlobalFields freeJoint

/-- Interval-independent difference control of the actual free critical coordinate.
This is derived from linearity and the retained numerical homogeneous bound. -/
theorem freeGradient_difference_norm_le (hD : OrdinaryH1Density)
    {K Ch : ℝ} (hS : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u v : EnergyState) (j : Fin 3) :
    ‖criticalGradient _ j (freeCriticalPath hD hS hfree a b u) -
      criticalGradient _ j (freeCriticalPath hD hS hfree a b v)‖ ≤ Ch * ‖u - v‖ := by
  let f : EnergyState → CriticalPath (intervalMeasure a b) :=
    freeCriticalPath hD hS hfree a b
  let G : CriticalPath (intervalMeasure a b) →L[ℂ] CriticalGradient (intervalMeasure a b) :=
    criticalGradient (intervalMeasure a b) j
  have hsub : f (u - v) = f u - f v :=
    actual_freeCriticalPath_sub hD hS hfree a b u v
  have hmap : G (f u - f v) = G (f u) - G (f v) :=
    G.toLinearMap.map_sub (f u) (f v)
  have hcoord : G (f u) - G (f v) = G (f (u - v)) :=
    hmap.symm.trans (congrArg (fun z : CriticalPath (intervalMeasure a b) => G z) hsub.symm)
  have hnorm : ‖G (f u) - G (f v)‖ = ‖G (f (u - v))‖ :=
    congrArg (fun z : CriticalGradient (intervalMeasure a b) => ‖z‖) hcoord
  have hb : ‖G (f (u - v))‖ ≤ Ch * ‖energyGradient j (u - v)‖ :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hfree.1 (norm_nonneg _))).mp
      ((ofReal_norm (G (f (u - v)))).le.trans
        (freeCriticalPath_gradient_bound hD hS hfree a b (u - v) j))
  exact hnorm.le.trans (hb.trans (mul_le_mul_of_nonneg_left
    (energyState_gradient_norm_le (u - v) j) hfree.1))

/-- Choose the finite common subradius before entering the heavy path types.
The empty finite set is included, so no nonempty-carrier premise is introduced. -/
private theorem finite_positive_subradius {X : Type*} (S : Set X) (hS : S.Finite)
    (r : X → ℝ) (hr : ∀ x, 0 < r x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S, δ < r x := by
  classical
  by_cases hSne : S.Nonempty
  · obtain ⟨v, _hv, hmin⟩ := Set.exists_min_image (α := X) (β := ℝ) S r hS hSne
    refine ⟨r v / 2, half_pos (hr v), ?_⟩
    intro x hx
    exact (half_lt_self (hr v)).trans_le (hmin x hx)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exact False.elim (hSne ⟨x, hx⟩)

/-- The compact-net argument is purely real-valued. Its proof never unfolds
an energy state, a Bochner space, or a path constructor. -/
private theorem compact_uniform_size_small {E : Type*} [NormedAddCommGroup E]
    {Q : Set E} (hQ : IsCompact Q) (F : ℝ → ℝ → E → Fin 3 → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hcompare : ∀ a b u v j, F a b u j ≤ C * ‖u - v‖ + F a b v j)
    (hlocal : ∀ u : E, ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∀ a b : ℝ, -r ≤ a → b ≤ r → ∀ j, F a b u j ≤ ε)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, -δ ≤ a → b ≤ δ →
      ∀ u ∈ Q, ∀ j, F a b u j ≤ η := by
  classical
  have hCp : 0 < C + 1 := by linarith
  let τ : ℝ := η / (2 * (C + 1))
  have hτ : 0 < τ := div_pos hη (by positivity)
  have herror : C * τ < η / 2 := by
    have hid : (C + 1) * τ = η / 2 := by
      dsimp [τ]
      field_simp [ne_of_gt hCp]
    nlinarith
  obtain ⟨S, _hSQ, hSfin, hcover⟩ := hQ.finite_cover_balls hτ
  let r : E → ℝ := fun u => Classical.choose (hlocal u (η / 2) (half_pos hη))
  have hr (u : E) : 0 < r u :=
    (Classical.choose_spec (hlocal u (η / 2) (half_pos hη))).1
  have hsmall (u : E) (a b : ℝ) :
      -r u ≤ a → b ≤ r u → ∀ j, F a b u j ≤ η / 2 :=
    (Classical.choose_spec (hlocal u (η / 2) (half_pos hη))).2 a b
  obtain ⟨δ, hδ, hbelow⟩ := finite_positive_subradius S hSfin r hr
  refine ⟨δ, hδ, ?_⟩
  intro a b ha hb u hu j
  obtain ⟨w, hw, huw⟩ : ∃ w ∈ S, u ∈ ball w τ := by
    simpa only [mem_iUnion, exists_prop] using hcover hu
  have hnear : ‖u - w‖ < τ := by
    simpa only [mem_ball, dist_eq_norm] using huw
  have hwa : -r w ≤ a := by linarith [hbelow w hw]
  have hwb : b ≤ r w := hb.trans (hbelow w hw).le
  calc
    F a b u j ≤ C * ‖u - w‖ + F a b w j := hcompare a b u w j
    _ ≤ C * τ + η / 2 := add_le_add
      (mul_le_mul_of_nonneg_left hnear.le hC) (hsmall w a b hwa hwb j)
    _ ≤ η := by linarith

/-- The size comparison still comes from the same actual critical coordinates. -/
private theorem freeGradient_size_compare (hD : OrdinaryH1Density)
    {K Ch : ℝ} (hS : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (a b : ℝ) (u v : EnergyState) (j : Fin 3) :
    ‖criticalGradient _ j (freeCriticalPath hD hS hfree a b u)‖ ≤
      Ch * ‖u - v‖ + ‖criticalGradient _ j (freeCriticalPath hD hS hfree a b v)‖ := by
  let U : CriticalGradient (intervalMeasure a b) :=
    criticalGradient (intervalMeasure a b) j (freeCriticalPath hD hS hfree a b u)
  let V : CriticalGradient (intervalMeasure a b) :=
    criticalGradient (intervalMeasure a b) j (freeCriticalPath hD hS hfree a b v)
  have hd : ‖U - V‖ ≤ Ch * ‖u - v‖ :=
    freeGradient_difference_norm_le hD hS hfree a b u v j
  exact (norm_le_norm_sub_add U V).trans (add_le_add hd (le_refl ‖V‖))

/-- Single-datum literal Fourier localization, kept outside the compact-net proof. -/
private theorem freeGradient_single_window (hD : OrdinaryH1Density)
    {K Ch : ℝ} (hS : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (u : EnergyState) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, -δ ≤ a → b ≤ δ → ∀ j : Fin 3,
      ‖criticalGradient _ j (freeCriticalPath hD hS hfree a b u)‖ ≤ ε := by
  obtain ⟨r, hr, hsmall⟩ := freeJoint_coordinates_local_smallness hfree u 0 ε hε
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro a b ha hb j
  have hsub : Set.Icc a b ⊆ Metric.ball (0 : ℝ) r := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have he : ENNReal.ofReal
      ‖criticalGradient (intervalMeasure a b) j (freeCriticalPath hD hS hfree a b u)‖ =
      mixedNorm (volume.restrict (Set.Icc a b)) volume 10 criticalExponent
        (freeJoint (energyGradient j u)) :=
    (ofReal_norm (criticalGradient (intervalMeasure a b) j
      (freeCriticalPath hD hS hfree a b u))).trans
        (freeCriticalPath_gradient_eq_restrict hD hS hfree a b u j)
  have hbnd : mixedNorm (volume.restrict (Set.Icc a b)) volume 10 criticalExponent
      (freeJoint (energyGradient j u)) ≤ ENNReal.ofReal ε :=
    (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)).trans (hsmall j)
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp (he.le.trans hbnd)

/-- A genuine finite compact net, coupled to literal Fourier time localization,
produces one time window valid for every datum and every smaller interval. -/
theorem compact_uniform_freeGradient_small (hD : OrdinaryH1Density)
    {K Ch : ℝ} (hS : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    {Q : Set EnergyState} (hQ : IsCompact Q) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a b : ℝ), -δ ≤ a → b ≤ δ →
      ∀ u ∈ Q, ∀ j : Fin 3,
        ‖criticalGradient _ j (freeCriticalPath hD hS hfree a b u)‖ ≤ η := by
  exact compact_uniform_size_small hQ
    (fun a b u j => ‖criticalGradient (intervalMeasure a b) j
      (freeCriticalPath hD hS hfree a b u)‖) hfree.1
    (freeGradient_size_compare hD hS hfree)
    (freeGradient_single_window hD hS hfree) hη

/-- Compactness supplies an actual common energy cap before either nonlinear radius.
The whole free evolution is controlled; there is no L2 value premise. -/
theorem compact_uniform_freeEnergy_cap (hD : OrdinaryH1Density)
    {K Ch : ℝ} (hS : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch)
    {Q : Set EnergyState} (hQ : IsCompact Q) :
    ∃ B : ℝ, 0 < B ∧ ∀ (a b : ℝ), ∀ u ∈ Q,
      ‖energyPath _ (freeCriticalPath hD hS hfree a b u)‖ ≤ B / 2 := by
  obtain ⟨M, hM, hbound⟩ := hQ.isBounded.exists_pos_norm_le
  let A : ℝ := max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨2 * (A + 1) * M, by positivity, ?_⟩
  intro a b u hu
  have henergy : ‖energyPath _ (freeCriticalPath hD hS hfree a b u)‖ ≤ A * ‖u‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hA (norm_nonneg _))).mpr
    intro t
    rw [freeCriticalPath_energy]
    exact freeEnergyState_norm_bound hD hS (t : ℝ) u
  have hcap := henergy.trans (mul_le_mul_of_nonneg_left (hbound u hu) hA)
  nlinarith

#print axioms freeGradient_difference_norm_le
#print axioms compact_uniform_freeGradient_small
#print axioms compact_uniform_freeEnergy_cap
end HartreeF.CompactUniformLifespan
