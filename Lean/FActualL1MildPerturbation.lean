import FActualL1ForcingDefect

/-! Small-interval perturbation with the literal L1 scalar / L2 gradient
error source. The input is the actual forced mild identity; producing it from
the distributional PDE and the long-time finite partition are separate nodes. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped NNReal Topology
namespace HartreeF.ActualPerturbation
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient hartreeDuhamelMap criticalPathIntervalSource

/-- The two small quantitative inputs are the true datum error and the true
gradient forcing norm. No contraction, small nonlinear source, fixed point,
or energy error identity is supplied as a premise. -/
theorem exists_actual_solution_of_small_forcing (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f g : EnergyState) (q : CriticalPath (intervalMeasure a b))
      (E : CompatibleL1IntervalSource a b),
      q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
        Complex.I • E.retardedCriticalPath hDensity hSob h0 hret →
      ‖energyPath _ q‖ ≤ B → ‖fun j => criticalGradient _ j q‖ ≤ r →
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ +
        max (energyEndpointConstant K C0) Cr * ‖E.gradient‖ ≤ r/2 →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsMildHartreePath hab alpha c f u ∧ FullZPath u ∧
        energyPath _ u ⟨a, le_rfl, hab⟩ = f ∧
        ‖u-q‖ ≤ 2 * (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖ +
          max (energyEndpointConstant K C0) Cr * ‖E.gradient‖) ∧
        ∀ v : CriticalPath (intervalMeasure a b),
          IsMildHartreePath hab alpha c f v → v=u := by
  let choice := exists_actual_solution_of_small_defect
    hDensity hSob h0 hfree hret hefree heret hH hB
  let r : ℝ := Classical.choose choice
  refine ⟨r, (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.1, ?_⟩
  intro a b hab f g q E hforced hqE hqW hsmall
  have hdef := actual_forced_mild_defect_bound hDensity hSob h0 hfree hret hH hab f g q E hforced
  let result := (Classical.choose_spec choice).2.2 hab f q hqE hqW (hdef.trans hsmall)
  let u : CriticalPath (intervalMeasure a b) := Classical.choose result
  have hu := Classical.choose_spec result
  exact ⟨u, hu.1, hu.2.1, hu.2.2.1,
    hu.2.2.2.1.trans (mul_le_mul_of_nonneg_left hdef (by norm_num)), hu.2.2.2.2⟩

#print axioms exists_actual_solution_of_small_forcing
end HartreeF.ActualPerturbation
