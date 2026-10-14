import FActualBackwardPerturbation
import FActualDuhamelDefectStability
import FL1AdvancedCriticalPath
import FBackwardHartreeDataDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped NNReal Topology
namespace HartreeF.BackwardPerturbation
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath ActualPerturbation
open CriticalUniqueness EndpointOutput FreeDataDependence BackwardUniformData
open ActualBackwardLocalFixedPoint
attribute [local instance] canonicalEnergyNormedSpace canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  backwardHartreeDuhamelMap criticalPathIntervalSource
  CompatibleL1IntervalSource.advancedCriticalPath

/-- Small defect for the actual negative-i terminal map produces the unique actual solution. -/
theorem exists_actual_backward_solution_of_small_defect (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f : EnergyState) (q : CriticalPath (intervalMeasure a b)),
      ‖energyPath _ q‖ ≤ B → ‖fun j => criticalGradient _ j q‖ ≤ r →
      ‖backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f q-q‖ ≤ r/2 →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsBackwardMildHartreePath hab alpha c f u ∧ FullZPath u ∧
        energyPath _ u ⟨b, hab, le_rfl⟩ = f ∧
        ‖u-q‖ ≤ 2*‖backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f q-q‖ ∧
        ∀ v : CriticalPath (intervalMeasure a b),
          IsBackwardMildHartreePath hab alpha c f v → v=u := by
  let choice := exists_actual_backward_small_perturbation hDensity hSob h0 hfree hret hH hB
  let r : ℝ := Classical.choose choice
  refine ⟨r, (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.1, ?_⟩
  intro a b hab f q hqE hqW hd
  let Φ := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f
  let wc := (Classical.choose_spec choice).2.2 hab f q (Φ q-q) hqE hqW hd
  let w : CriticalPath (intervalMeasure a b) := Classical.choose wc
  have hw := (Classical.choose_spec wc).2.1
  have hwest : ‖w‖ ≤ 2*‖Φ q-q‖ := (Classical.choose_spec wc).2.2
  have hfix : Φ (q+w)=q+w := defect_increment_fixedPoint Φ q w hw
  have hmild := (isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab f (q+w)).mpr hfix
  have hfull : FullZPath (q+w) := by
    exact (congrArg (fun v : CriticalPath (intervalMeasure a b) => FullZPath v) hfix).mp
      ⟨backwardHartreeDuhamelMap_endpointWitness hDensity hSob h0 hfree hret hefree heret hH hab f (q+w)⟩
  refine ⟨q+w, hmild, hfull,
    actual_backward_fixedPoint_terminal hDensity hSob h0 hfree hret hH hab f (q+w) hfix, ?_, ?_⟩
  · exact (congrArg norm (add_sub_cancel_left q w)).trans_le hwest
  · intro v hv
    exact actual_backward_criticalPath_fixedPoint_unique hDensity hSob h0 hfree hret hH hab f v (q+w)
      ((isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab f v).mp hv) hfix

/-- The forced backward identity has +i A(e), hence its defect has -i A(e). -/
theorem actual_backward_forced_defect_bound (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (f g : EnergyState) (q : CriticalPath (intervalMeasure a b))
    (E : CompatibleL1IntervalSource a b)
    (hforced : q = backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q +
      Complex.I • E.advancedCriticalPath hDensity hSob h0 hfree hret) :
    ‖backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f q-q‖ ≤
      max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch * ‖f-g‖ +
        max (energyEndpointConstant K C0) (Ch*C0+Cr) * ‖E.gradient‖ := by
  let Φ := backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
  let A := E.advancedCriticalPath hDensity hSob h0 hfree hret
  have heq : Φ f q-q=(Φ f q-Φ g q)-Complex.I • A :=
    (congrArg (fun v : CriticalPath (intervalMeasure a b) => Φ f q-v) hforced).trans
      (sub_add_eq_sub_sub (Φ f q) (Φ g q) (Complex.I • A))
  have hdata : ‖Φ f q-Φ g q‖ ≤ max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch * ‖f-g‖ :=
    (congrArg norm (actual_backwardHartreeDuhamelMap_data_sub hDensity hSob h0 hfree hret hH hab f g q)).trans_le
      (actual_backwardFreeCriticalPath_norm_le hDensity hSob hfree a b (f-g))
  exact (congrArg norm heq).trans_le ((norm_sub_le _ _).trans (add_le_add hdata
    ((complexUnit_norm A).trans_le (E.advancedCriticalPath_norm_le hDensity hSob h0 hfree hret))))

/-- Backward small-forcing stability for scalar L1 and actual gradient L2 errors. -/
theorem exists_actual_backward_solution_of_small_forcing (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f g : EnergyState) (q : CriticalPath (intervalMeasure a b))
      (E : CompatibleL1IntervalSource a b),
      q = backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q +
        Complex.I • E.advancedCriticalPath hDensity hSob h0 hfree hret →
      ‖energyPath _ q‖ ≤ B → ‖fun j => criticalGradient _ j q‖ ≤ r →
      max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch * ‖f-g‖ +
        max (energyEndpointConstant K C0) (Ch*C0+Cr) * ‖E.gradient‖ ≤ r/2 →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsBackwardMildHartreePath hab alpha c f u ∧ FullZPath u ∧
        energyPath _ u ⟨b,hab,le_rfl⟩ = f ∧
        ‖u-q‖ ≤ 2*(max (max (K^((6 : ℝ)⁻¹)) 1*Real.sqrt 3) Ch * ‖f-g‖ +
          max (energyEndpointConstant K C0) (Ch*C0+Cr) * ‖E.gradient‖) ∧
        ∀ v : CriticalPath (intervalMeasure a b), IsBackwardMildHartreePath hab alpha c f v → v=u := by
  let choice := exists_actual_backward_solution_of_small_defect hDensity hSob h0 hfree hret hefree heret hH hB
  let r : ℝ := Classical.choose choice
  refine ⟨r, (Classical.choose_spec choice).1, (Classical.choose_spec choice).2.1, ?_⟩
  intro a b hab f g q E hforced hqE hqW hsmall
  have hd := actual_backward_forced_defect_bound hDensity hSob h0 hfree hret hH hab f g q E hforced
  let result := (Classical.choose_spec choice).2.2 hab f q hqE hqW (hd.trans hsmall)
  let u : CriticalPath (intervalMeasure a b) := Classical.choose result
  have hu := Classical.choose_spec result
  exact ⟨u, hu.1, hu.2.1, hu.2.2.1,
    hu.2.2.2.1.trans (mul_le_mul_of_nonneg_left hd (by norm_num)), hu.2.2.2.2⟩

end HartreeF.BackwardPerturbation
