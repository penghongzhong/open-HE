import FFreeCriticalPastTail
import FUniformForwardInitialSolver
import FMildHartreeDefinition
import FActualCriticalPathUniqueness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.WaveInitial
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource restrictPath IsMildHartreePath

/-- Prescribed homogeneous asymptotic data yield actual initial solutions on
all sufficiently early compact intervals. Energy cap B is independent of the
requested tolerance and of both interval endpoints. No solution at infinity
or prior scattering property is an input. -/
theorem exists_negative_initial_approximations (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) :
    ∃ B : ℝ, 0<B ∧ ∀ delta : ℝ, 0<delta →
      ∃ eta T : ℝ, 0<eta ∧ eta≤delta ∧ ∀ R A : ℝ, A≤T → ∀ hRA : R≤A,
      ∃ u : CriticalPath (intervalMeasure R A),
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hRA
          (freeEnergyState hDensity hSob R phi) u=u ∧
        energyPath _ u ⟨R,le_rfl,hRA⟩=freeEnergyState hDensity hSob R phi ∧
        IsMildHartreePath hRA alpha kernel (freeEnergyState hDensity hSob R phi) u ∧
        ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤eta ∧
        ‖u-freeCriticalPath hDensity hSob hfree R A phi‖≤eta/2 := by
  let E0 := (max (K^((6:ℝ)⁻¹)) 1*Real.sqrt 3)*‖phi‖
  have hE0 : 0≤E0 := by dsimp [E0]; positivity
  let B := 2*E0+1
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro delta hdelta
  let chosen := exists_uniform_forward_initial_radius hDensity hSob h0 hfree hret hH hB hdelta
  let eta : ℝ := Classical.choose chosen
  have heta : 0<eta := (Classical.choose_spec chosen).1
  have hetad : eta≤delta := (Classical.choose_spec chosen).2.1
  let tailChoice := exists_freeCriticalPath_past_small hDensity hSob hfree phi
    (show 0<eta/2 by positivity)
  let T : ℝ := Classical.choose tailChoice
  refine ⟨eta,T,heta,hetad,?_⟩
  intro R A hAT hRA
  have hcancel : freeEnergyState hDensity hSob (-R)
      (freeEnergyState hDensity hSob R phi)=phi := freeEnergyState_left_inverse hDensity hSob R phi
  have hE : ‖energyPath _ (freeCriticalPath hDensity hSob hfree R A
      (freeEnergyState hDensity hSob (-R) (freeEnergyState hDensity hSob R phi)))‖≤B/2 := by
    rw [hcancel]
    have he : ‖energyPath _ (freeCriticalPath hDensity hSob hfree R A phi)‖≤E0 := by
      apply (ContinuousMap.norm_le _ hE0).mpr
      intro t
      rw [freeCriticalPath_energy]
      exact freeEnergyState_norm_bound hDensity hSob t phi
    exact he.trans (by dsimp [B]; linarith)
  have hW : ∀ j : Fin 3, ‖criticalGradient _ j (freeCriticalPath hDensity hSob hfree R A
      (freeEnergyState hDensity hSob (-R) (freeEnergyState hDensity hSob R phi)))‖≤eta/2 := by
    rw [hcancel]
    exact (Classical.choose_spec tailChoice) R A hAT hRA
  let solved := (Classical.choose_spec chosen).2.2 hRA
    (freeEnergyState hDensity hSob R phi) hE hW
  let u : CriticalPath (intervalMeasure R A) := Classical.choose solved
  have hfix := (Classical.choose_spec solved).1
  have hterminal := (Classical.choose_spec solved).2.1
  have huE := (Classical.choose_spec solved).2.2.1
  have huW := (Classical.choose_spec solved).2.2.2.1
  have herror : ‖u-freeCriticalPath hDensity hSob hfree R A
      (freeEnergyState hDensity hSob (-R) (freeEnergyState hDensity hSob R phi))‖≤eta/2 :=
    (Classical.choose_spec solved).2.2.2.2
  have hefree := congrArg (freeCriticalPath hDensity hSob hfree R A) hcancel
  have herr : ‖u-freeCriticalPath hDensity hSob hfree R A phi‖≤eta/2 :=
    (congrArg (fun v : CriticalPath (intervalMeasure R A) => ‖u-v‖) hefree).symm.le.trans herror
  refine ⟨u,hfix,hterminal,?_,huE,huW,herr⟩
  exact (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hRA
    (freeEnergyState hDensity hSob R phi) u).mpr hfix

/-- For one initial cutoff, constructions with different right endpoints agree
on their overlap by actual forward uniqueness. No initial-cutoff limit is
asserted. -/
theorem initial_approximations_right_restriction (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel R A B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hRA : R≤A) (hAB : A≤B) (phi : EnergyState)
    (u : CriticalPath (intervalMeasure R B)) (v : CriticalPath (intervalMeasure R A))
    (hu : hartreeDuhamelMap hDensity hSob h0 hfree hret hH (hRA.trans hAB)
      (freeEnergyState hDensity hSob R phi) u=u)
    (hv : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hRA
      (freeEnergyState hDensity hSob R phi) v=v) :
    restrictPath le_rfl hRA hAB u=v := by
  have ht := actual_fixedPoint_initial hDensity hSob h0 hfree hret hH
    (hRA.trans hAB) (freeEnergyState hDensity hSob R phi) u hu
  have hr := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    le_rfl hRA hAB (freeEnergyState hDensity hSob R phi) u hu
  rw [ht] at hr
  exact actual_criticalPath_fixedPoint_unique hDensity hSob h0 hfree hret hH hRA
    (freeEnergyState hDensity hSob R phi) (restrictPath le_rfl hRA hAB u) v hr hv

end HartreeF.WaveInitial
