import FActualHartreePerturbation
import FActualCriticalPathUniqueness
import FMildHartreeDefinition
import FEndpointHartreeDuhamelOutput

/-! Actual finite-interval Hartree stability from a small literal Duhamel
defect. The resulting solution, initial trace, uniqueness and full-Z membership
are constructed. Producing the defect bound from a distributional forcing and
performing the long-time iteration remain subsequent steps. -/
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

theorem defect_increment_fixedPoint {E : Type*} [AddCommGroup E]
    (Φ : E → E) (q w : E) (hw : (Φ q-q)+(Φ (q+w)-Φ q)=w) :
    Φ (q+w) = q+w := by
  calc
    Φ (q+w) = q+((Φ q-q)+(Φ (q+w)-Φ q)) := by abel
    _ = q+w := congrArg (fun z => q+z) hw

/-- The defect is evaluated on the same actual Hartree map, datum and path. -/
def mildDefect (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hab : a ≤ b) (f : EnergyState) (q : CriticalPath (intervalMeasure a b)) :
    CriticalPath (intervalMeasure a b) :=
  hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f q - q

/-- Small actual Duhamel defect gives a genuine unique full-Z Hartree path
on the whole prescribed compact interval, quantitatively close in E+W. -/
theorem exists_actual_solution_of_small_defect (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ {a b : ℝ} (hab : a ≤ b)
      (f : EnergyState) (q : CriticalPath (intervalMeasure a b)),
      ‖energyPath _ q‖ ≤ B → ‖fun j => criticalGradient _ j q‖ ≤ r →
      ‖mildDefect hDensity hSob h0 hfree hret hH hab f q‖ ≤ r/2 →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsMildHartreePath hab alpha c f u ∧ FullZPath u ∧
        energyPath _ u ⟨a, le_rfl, hab⟩ = f ∧
        ‖u-q‖ ≤ 2 * ‖mildDefect hDensity hSob h0 hfree hret hH hab f q‖ ∧
        ∀ v : CriticalPath (intervalMeasure a b),
          IsMildHartreePath hab alpha c f v → v=u := by
  let choice := exists_actual_small_perturbation hDensity hSob h0 hfree hret hH hB
  let r : ℝ := Classical.choose choice
  have hr : 0 < r := (Classical.choose_spec choice).1
  have hr1 : r ≤ 1 := (Classical.choose_spec choice).2.1
  refine ⟨r, hr, hr1, ?_⟩
  intro a b hab f q hqE hqW hdef
  let d := mildDefect hDensity hSob h0 hfree hret hH hab f q
  let wc := (Classical.choose_spec choice).2.2 hab q d hqE hqW hdef
  let w : CriticalPath (intervalMeasure a b) := Classical.choose wc
  have hwfix := (Classical.choose_spec wc).2.1
  have hwest : ‖w‖ ≤ 2*‖d‖ := (Classical.choose_spec wc).2.2
  let Φ := hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f
  have hincrement : perturbationIncrement hDensity hSob h0 hfree hret hH hab q w =
      Φ (q+w)-Φ q :=
    (hartreeDuhamelMap_sub hDensity hSob h0 hfree hret hH hab 0 (q+w) q).trans
      (hartreeDuhamelMap_sub hDensity hSob h0 hfree hret hH hab f (q+w) q).symm
  have hw : (Φ q-q)+(Φ (q+w)-Φ q)=w :=
    (congrArg (fun z : CriticalPath (intervalMeasure a b) => d+z) hincrement).symm.trans hwfix
  have hfix : Φ (q+w)=q+w := defect_increment_fixedPoint Φ q w hw
  have hmild : IsMildHartreePath hab alpha c f (q+w) :=
    (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab f (q+w)).mpr hfix
  have hfull : FullZPath (q+w) :=
    fixedPoint_fullZ hDensity hSob h0 hfree hret hefree heret hH hab f (q+w) hfix
  have hinit : energyPath _ (q+w) ⟨a, le_rfl, hab⟩ = f :=
    actual_fixedPoint_initial hDensity hSob h0 hfree hret hH hab f (q+w) hfix
  refine ⟨q+w, hmild, hfull, hinit, ?_, ?_⟩
  · exact (congrArg norm (add_sub_cancel_left q w)).trans_le hwest
  · intro v hv
    exact actual_criticalPath_fixedPoint_unique hDensity hSob h0 hfree hret hH hab f v (q+w)
      ((isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab f v).mp hv) hfix

#print axioms defect_increment_fixedPoint
#print axioms mildDefect
#print axioms exists_actual_solution_of_small_defect
end HartreeF.ActualPerturbation
