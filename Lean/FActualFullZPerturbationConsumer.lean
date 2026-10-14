import FActualFullZForcingPerturbation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualPerturbationConsumer
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput FreeDataDependence TimeHolder ActualPerturbation
attribute [local instance] ActualPerturbation.canonicalEnergyNormedSpace
  ActualPerturbation.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  hartreeDuhamelMap criticalPathIntervalSource CompatibleL1IntervalSource.retardedCriticalPath

/-- This consumer extracts each actual endpoint/S quantity and both graph
coordinates from one bound on the same pair of paths. -/
theorem fullZSDifference_controls_actual_components {a b M : ℝ}
    (u q : CriticalPath (intervalMeasure a b)) (hM : 0 ≤ M)
    (h : fullZSDifferenceSize u q ≤ ENNReal.ofReal M) :
    ‖energyPath (intervalMeasure a b) (u-q)‖ ≤ M ∧
    (∀ j : Fin 3, ‖criticalGradient (intervalMeasure a b) j (u-q)‖ ≤ M) ∧
    mixedNorm (intervalMeasure a b) volume 2 6
      (fun t x => energyComplexGradient (energyPath _ u t) x -
        energyComplexGradient (energyPath _ q t) x) ≤ ENNReal.ofReal M ∧
    mixedNorm (intervalMeasure a b) volume 10 10
      (fun t x => energyValue (energyPath _ u t) x - energyValue (energyPath _ q t) x) ≤
        ENNReal.ofReal M := by
  have hn : ENNReal.ofReal ‖u-q‖ ≤ ENNReal.ofReal M :=
    (le_add_right (le_add_right le_rfl)).trans h
  have hr : ‖u-q‖ ≤ M := (ENNReal.ofReal_le_ofReal_iff hM).mp hn
  exact ⟨(energyPath_norm_le _ _).trans hr,
    fun j => (criticalGradient_norm_le _ _ j).trans hr,
    (le_add_right (le_add_left le_rfl)).trans h, (le_add_left le_rfl).trans h⟩

/-- The uniform theorem is consumed with its actual scalar-L1 error object;
zero datum and gradient errors recover the reference path exactly. -/
theorem zero_error_recovers_reference (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (g : EnergyState) (q : CriticalPath (intervalMeasure a b))
      (E : CompatibleL1IntervalSource a b),
      q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
        Complex.I • E.retardedCriticalPath hDensity hSob h0 hret →
      ‖energyPath _ q‖ ≤ B → ‖fun j => criticalGradient _ j q‖ ≤ r →
      E.gradient = 0 →
      IsMildHartreePath hab alpha c g q ∧ FullZPath q ∧
      energyPath _ q ⟨a, le_rfl, hab⟩ = g ∧
      fullZSDifferenceSize q q = 0 := by
  let theoremChoice := exists_actual_solution_fullZ_of_small_forcing
    hDensity hSob h0 hfree hret hefree heret hH hB
  let r : ℝ := Classical.choose theoremChoice
  let constantChoice := Classical.choose_spec theoremChoice
  let C : ℝ := Classical.choose constantChoice
  have spec := Classical.choose_spec constantChoice
  have hr : 0 < r := spec.1
  have hr1 : r ≤ 1 := spec.2.1
  refine ⟨r, hr, hr1, ?_⟩
  intro a b hab g q E hforced hqE hqW hE
  have hg0 : ‖g-g‖ = 0 := by simp only [sub_self, @norm_zero EnergyState _]
  have he0 : ‖E.gradient‖ = 0 := (congrArg norm hE).trans
    (@norm_zero (Fin 3 → LocalEndpointSource (Set.Icc a b)) _)
  have hsmall : max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖g-g‖ +
      max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ ≤ r/2 := by
    rw [hg0, he0, mul_zero, mul_zero, add_zero]
    exact (half_pos hr).le
  let result := spec.2.2.2 hab g g q E hforced hqE hqW hsmall
  let u : CriticalPath (intervalMeasure a b) := Classical.choose result
  have hu := Classical.choose_spec result
  have hmild := hu.1
  have hZ := hu.2.1
  have hinit := hu.2.2.2.1
  have hclose : ‖u-q‖ ≤ 2*(max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖g-g‖ +
      max (energyEndpointConstant K C0) Cr * ‖E.gradient‖) := hu.2.2.2.2.1
  have hfull : fullZSDifferenceSize u q ≤ ENNReal.ofReal (C*(‖g-g‖+‖E.gradient‖)) :=
    hu.2.2.2.2.2.1
  have hn : ‖u-q‖ ≤ 0 := by simpa only [hg0, he0, mul_zero, add_zero] using hclose
  have heq : u=q := sub_eq_zero.mp
    ((@norm_eq_zero (CriticalPath (intervalMeasure a b)) _ (u-q)).mp
      (le_antisymm hn (norm_nonneg (u-q))))
  refine ⟨heq ▸ hmild, heq ▸ hZ, heq ▸ hinit, ?_⟩
  exact le_antisymm (by simpa only [heq, hg0, he0, add_zero, mul_zero,
    ENNReal.ofReal_zero] using hfull) bot_le

/-- End-to-end consumer for nonzero data and original L1 forcing errors.
The output controls each actual component of the constructed same solution. -/
theorem small_forcing_constructed_full_components (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f g : EnergyState) (q : CriticalPath (intervalMeasure a b))
      (E : CompatibleL1IntervalSource a b),
      q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
        Complex.I • E.retardedCriticalPath hDensity hSob h0 hret →
      ‖energyPath _ q‖ ≤ B → ‖fun j => criticalGradient _ j q‖ ≤ r →
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ +
        max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ ≤ r/2 →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsMildHartreePath hab alpha c f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
        energyPath _ u ⟨a, le_rfl, hab⟩ = f ∧
        ‖u-q‖ ≤ 2 * (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ +
          max (energyEndpointConstant K C0) Cr * ‖E.gradient‖) ∧
        (‖energyPath (intervalMeasure a b) (u-q)‖ ≤ C*(‖f-g‖+‖E.gradient‖) ∧
        (∀ j : Fin 3, ‖criticalGradient (intervalMeasure a b) j (u-q)‖ ≤
          C*(‖f-g‖+‖E.gradient‖)) ∧
        mixedNorm (intervalMeasure a b) volume 2 6
          (fun t x => energyComplexGradient (energyPath _ u t) x -
            energyComplexGradient (energyPath _ q t) x) ≤
              ENNReal.ofReal (C*(‖f-g‖+‖E.gradient‖)) ∧
        mixedNorm (intervalMeasure a b) volume 10 10
          (fun t x => energyValue (energyPath _ u t) x - energyValue (energyPath _ q t) x) ≤
            ENNReal.ofReal (C*(‖f-g‖+‖E.gradient‖))) ∧
        ∀ v : CriticalPath (intervalMeasure a b),
          IsMildHartreePath hab alpha c f v → v=u := by
  let choice := exists_actual_solution_fullZ_of_small_forcing
    hDensity hSob h0 hfree hret hefree heret hH hB
  let r : ℝ := Classical.choose choice
  let cc := Classical.choose_spec choice
  let C : ℝ := Classical.choose cc
  have hs := Classical.choose_spec cc
  have hC : 0 < C := hs.2.2.1
  refine ⟨r, C, hs.1, hs.2.1, hC, ?_⟩
  intro a b hab f g q E hforced hqE hqW hsmall
  let result := hs.2.2.2 hab f g q E hforced hqE hqW hsmall
  let u : CriticalPath (intervalMeasure a b) := Classical.choose result
  have hu := Classical.choose_spec result
  have hM : 0 ≤ C*(‖f-g‖+‖E.gradient‖) :=
    mul_nonneg hC.le (add_nonneg (norm_nonneg (f-g)) (norm_nonneg E.gradient))
  exact ⟨u, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1,
    fullZSDifference_controls_actual_components u q hM hu.2.2.2.2.2.1,
    hu.2.2.2.2.2.2⟩

end HartreeF.ActualPerturbationConsumer
