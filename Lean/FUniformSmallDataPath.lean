import FActualDuhamelDefectStability
import FActualFreePathDifference

/-! A genuinely uniform small-data construction on any prescribed compact
interval. This is the positive small-energy seed, not the full W threshold. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.SmallEnergy
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath
open CriticalUniqueness EndpointOutput ActualPerturbation FreeDataDependence
attribute [local instance] ActualPerturbation.canonicalEnergyNormedSpace
  ActualPerturbation.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  energyPath criticalGradient hartreeDuhamelMap criticalPathIntervalSource
  freeCriticalPath freeEnergyState

theorem hartreeDuhamelMap_zero_path (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (f : EnergyState) :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f 0 =
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) f) := by
  have hzero : Complex.I • intervalRetardedCriticalPath hDensity hSob h0 hret
      (criticalPathIntervalSource hDensity hSob hH hab 0 0) = 0 :=
    (hartreeDuhamelMap_sub hDensity hSob h0 hfree hret hH hab 0 0 0).symm.trans
      (sub_self (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab 0 0))
  unfold hartreeDuhamelMap
  exact (congrArg (fun z : CriticalPath (intervalMeasure a b) =>
    freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) f)+z) hzero).trans
      (add_zero _)

theorem mildDefect_zero_path_norm_le (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (f : EnergyState) :
    ‖mildDefect hDensity hSob h0 hfree hret hH hab f 0‖ ≤
      max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f‖ := by
  have heq : mildDefect hDensity hSob h0 hfree hret hH hab f 0 =
      freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) f) :=
    (sub_zero (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f 0)).trans
      (hartreeDuhamelMap_zero_path hDensity hSob h0 hfree hret hH hab f)
  exact (congrArg norm heq).trans_le
    (actual_shiftedFreeCriticalPath_norm_le hDensity hSob hfree a b f)

/-- The same positive datum radius works on every finite interval, with no
interval length, initial mass, or pre-existing small nonlinear solution input. -/
theorem exists_uniform_small_data_path (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {a b : ℝ} (hab : a ≤ b) (f : EnergyState),
      ‖f‖ ≤ delta → ∃ u : CriticalPath (intervalMeasure a b),
        IsMildHartreePath hab alpha c f u ∧ FullZPath u ∧
        ‖u‖ ≤ 2 * (max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f‖) ∧
        ∀ v : CriticalPath (intervalMeasure a b),
          IsMildHartreePath hab alpha c f v → v=u := by
  let choice := exists_actual_solution_of_small_defect
    hDensity hSob h0 hfree hret hefree heret hH (B := 0) le_rfl
  let r : ℝ := Classical.choose choice
  have hr : 0 < r := (Classical.choose_spec choice).1
  let Cf := max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch
  have hCf : 0 ≤ Cf := hfree.1.trans (le_max_right _ _)
  let delta := r / (2*(Cf+1))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hCd : Cf*delta ≤ r/2 := by
    dsimp [delta]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2*(Cf+1))).mpr
    nlinarith
  refine ⟨delta, hdelta, ?_⟩
  intro a b hab f hf
  have hdef := mildDefect_zero_path_norm_le hDensity hSob h0 hfree hret hH hab f
  have hsmall : ‖mildDefect hDensity hSob h0 hfree hret hH hab f 0‖ ≤ r/2 :=
    hdef.trans ((mul_le_mul_of_nonneg_left hf hCf).trans hCd)
  have hE : ‖energyPath (intervalMeasure a b) 0‖ ≤ (0 : ℝ) := by
    have hz : ‖(0 : C(Set.Icc a b, EnergyState))‖ = 0 := norm_zero (E := C(Set.Icc a b, EnergyState))
    exact le_of_eq ((congrArg norm ((energyPath (intervalMeasure a b)).map_zero)).trans hz)
  have hW : ‖fun j => criticalGradient (intervalMeasure a b) j 0‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg hr.le).mpr
    intro j
    have hz : ‖(0 : CriticalGradient (intervalMeasure a b))‖ = 0 := norm_zero (E := CriticalGradient (intervalMeasure a b))
    exact (le_of_eq ((congrArg norm ((criticalGradient (intervalMeasure a b) j).map_zero)).trans hz)).trans hr.le
  let result := (Classical.choose_spec choice).2.2 hab f 0 hE hW hsmall
  let u : CriticalPath (intervalMeasure a b) := Classical.choose result
  have hu := Classical.choose_spec result
  have hnorm : ‖u‖ ≤ 2 * (Cf*‖f‖) :=
    ((congrArg norm (sub_zero u)).symm.trans_le hu.2.2.2.1).trans
      (mul_le_mul_of_nonneg_left hdef (by norm_num))
  exact ⟨u, hu.1, hu.2.1, hnorm, hu.2.2.2.2⟩

#print axioms hartreeDuhamelMap_zero_path
#print axioms mildDefect_zero_path_norm_le
#print axioms exists_uniform_small_data_path
end HartreeF.SmallEnergy
