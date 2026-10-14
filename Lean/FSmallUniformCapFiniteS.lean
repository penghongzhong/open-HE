import FUniformSmallDataPath
import FMaximalFiniteSGlobalScattering

/-! A small actual state cap produces a genuine finite S bound by constructing
small solutions on arbitrary compact intervals and identifying the same
trajectory by uniqueness. No S or W bound is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.SmallEnergy
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput CriticalSourceBounds MaximalTrajectory
open MaximalFiniteSGlobal
attribute [local instance] ActualPerturbation.canonicalEnergyNormedSpace
  ActualPerturbation.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient

theorem exists_small_state_cap_uniformS (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ M : ℝ≥0, ∀ {s0 : ℝ} {u0 : EnergyState}
      (U : LocalMildTrajectory alpha c s0 u0),
      (∀ t ∈ U.domain, ‖U.state t‖ ≤ delta) → UniformCompactS U M := by
  let choice := exists_uniform_small_data_path hDensity hSob h0 hfree hret hefree heret hH
  let delta : ℝ := Classical.choose choice
  have hdelta : 0 < delta := (Classical.choose_spec choice).1
  let Cf := max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  let eta := 2*(Cf*delta)
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  let M : ℝ≥0 := Real.toNNReal (normComparisonConstant K * eta)
  refine ⟨delta, hdelta, M, ?_⟩
  intro s0 u0 U hcap a b hab hI
  have ha : a ∈ U.domain := hI ⟨le_rfl, hab⟩
  let result := (Classical.choose_spec choice).2 hab (U.state a) (hcap a ha)
  let v : CriticalPath (intervalMeasure a b) := Classical.choose result
  have hv := Classical.choose_spec result
  have heq : U.path hab hI = v := hv.2.2.2 (U.path hab hI) (U.path_mild hab hI)
  have hnorm : ‖U.path hab hI‖ ≤ eta :=
    (congrArg norm heq).trans_le (hv.2.2.1.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcap a ha) hCf) (by norm_num)))
  have hcoords : ‖fun j => criticalGradient (intervalMeasure a b) j (U.path hab hI)‖ ≤ eta := by
    apply (pi_norm_le_iff_of_nonneg heta).mpr
    intro j
    exact (criticalGradient_norm_le _ (U.path hab hI) j).trans hnorm
  have hS := (path_sizes_le_coordinate_cap (intervalMeasure a b) hDensity hSob heta
    (U.path hab hI) hcoords).2
  exact hS

theorem exists_small_state_cap_implies_finiteS (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {s0 : ℝ} {u0 : EnergyState}
      (U : LocalMildTrajectory alpha c s0 u0),
      (∀ t ∈ U.domain, ‖U.state t‖ ≤ delta) → FiniteSOnDomain U := by
  let choice := exists_small_state_cap_uniformS hDensity hSob h0 hfree hret hefree heret hH
  let delta : ℝ := Classical.choose choice
  have hd : 0 < delta := (Classical.choose_spec choice).1
  let mc := (Classical.choose_spec choice).2
  let M : ℝ≥0 := Classical.choose mc
  refine ⟨delta, hd, ?_⟩
  intro s0 u0 U hcap
  exact ⟨M, (Classical.choose_spec mc) U hcap⟩

#print axioms exists_small_state_cap_uniformS
#print axioms exists_small_state_cap_implies_finiteS
end HartreeF.SmallEnergy
