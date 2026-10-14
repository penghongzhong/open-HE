import FForcedSmallSGraphBound

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcedSmallS
open EnergySpace CriticalPathSpace CriticalSourceBounds ActualDuhamelPath
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
attribute [local instance] ActualPerturbation.canonicalEnergyNormedSpace
  ActualPerturbation.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath

/-- Uniform preliminary graph bound for the approximate trajectory on a
small-S piece, anchored at its own actual initial state. This needs only
the original error gradient bound and never assumes a W bound. -/
theorem exists_small_s_uniform_approximate_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hB : 0 ≤ B) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b),
      q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
        (energyPath _ q ⟨a, le_rfl, hab⟩) q -
        Complex.I • E.retardedCriticalPath hDensity hSob h0 hret →
      ‖energyPath (intervalMeasure a b) q‖ ≤ B →
      pathValueSize (intervalMeasure a b) q ≤ ENNReal.ofReal eta →
      ‖E.gradient‖ ≤ 1 →
      ‖q‖ ≤ 2 * (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * B +
        max (energyEndpointConstant K C0) Cr) := by
  let choice := exists_small_s_forced_graph_bound hDensity hSob h0 hfree hret hH hB
  let eta : ℝ := Classical.choose choice
  refine ⟨eta, (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.1, ?_⟩
  intro a b hab q E hforced hE hS herr
  have hg : ‖energyPath _ q ⟨a, le_rfl, hab⟩‖ ≤ B :=
    ((energyPath _ q).norm_coe_le_norm ⟨a, le_rfl, hab⟩).trans hE
  have hbound := (Classical.choose_spec choice).2.2 hab
    (energyPath _ q ⟨a, le_rfl, hab⟩) q E hforced hE hS
  have hCf : 0 ≤ max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch :=
    hfree.1.trans (le_max_right _ _)
  have hQ : 0 ≤ max (energyEndpointConstant K C0) Cr :=
    (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hg hCf)
    (mul_le_mul_of_nonneg_left herr hQ)
  rw [mul_one] at hsum
  exact hbound.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))

#print axioms exists_small_s_uniform_approximate_bound
end HartreeF.ForcedSmallS
