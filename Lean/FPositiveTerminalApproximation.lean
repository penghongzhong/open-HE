import FFreeCriticalFutureTail
import FUniformBackwardTerminalSolver
import FMildHartreeDefinition

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.WaveTerminal
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  freeCriticalPath backwardHartreeDuhamelMap hartreeDuhamelMap criticalPathIntervalSource restrictPath IsMildHartreePath

/-- Prescribed homogeneous asymptotic data yield actual terminal solutions on
all sufficiently late compact intervals. Energy cap B is independent of the
requested tolerance and of both interval endpoints. No solution at infinity
or prior scattering property is an input. -/
theorem exists_positive_terminal_approximations (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) :
    ∃ B : ℝ, 0<B ∧ ∀ delta : ℝ, 0<delta →
      ∃ eta T : ℝ, 0<eta ∧ eta≤delta ∧ ∀ A R : ℝ, T≤A → ∀ hAR : A≤R,
      ∃ u : CriticalPath (intervalMeasure A R),
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hAR
          (freeEnergyState hDensity hSob R phi) u=u ∧
        energyPath _ u ⟨R,hAR,le_rfl⟩=freeEnergyState hDensity hSob R phi ∧
        IsMildHartreePath hAR alpha kernel (energyPath _ u ⟨A,le_rfl,hAR⟩) u ∧
        ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤eta ∧
        ‖u-freeCriticalPath hDensity hSob hfree A R phi‖≤eta/2 := by
  let E0 := (max (K^((6:ℝ)⁻¹)) 1*Real.sqrt 3)*‖phi‖
  have hE0 : 0≤E0 := by dsimp [E0]; positivity
  let B := 2*E0+1
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro delta hdelta
  let chosen := exists_uniform_backward_terminal_radius hDensity hSob h0 hfree hret hH hB hdelta
  let eta : ℝ := Classical.choose chosen
  have heta : 0<eta := (Classical.choose_spec chosen).1
  have hetad : eta≤delta := (Classical.choose_spec chosen).2.1
  let tailChoice := exists_freeCriticalPath_future_small hDensity hSob hfree phi
    (show 0<eta/2 by positivity)
  let T : ℝ := Classical.choose tailChoice
  refine ⟨eta,T,heta,hetad,?_⟩
  intro A R hTA hAR
  have hcancel : freeEnergyState hDensity hSob (-R)
      (freeEnergyState hDensity hSob R phi)=phi := freeEnergyState_left_inverse hDensity hSob R phi
  have hE : ‖energyPath _ (freeCriticalPath hDensity hSob hfree A R
      (freeEnergyState hDensity hSob (-R) (freeEnergyState hDensity hSob R phi)))‖≤B/2 := by
    rw [hcancel]
    have he : ‖energyPath _ (freeCriticalPath hDensity hSob hfree A R phi)‖≤E0 := by
      apply (ContinuousMap.norm_le _ hE0).mpr
      intro t
      rw [freeCriticalPath_energy]
      exact freeEnergyState_norm_bound hDensity hSob t phi
    exact he.trans (by dsimp [B]; linarith)
  have hW : ∀ j : Fin 3, ‖criticalGradient _ j (freeCriticalPath hDensity hSob hfree A R
      (freeEnergyState hDensity hSob (-R) (freeEnergyState hDensity hSob R phi)))‖≤eta/2 := by
    rw [hcancel]
    exact (Classical.choose_spec tailChoice) A R hTA hAR
  let solved := (Classical.choose_spec chosen).2.2 hAR
    (freeEnergyState hDensity hSob R phi) hE hW
  let u : CriticalPath (intervalMeasure A R) := Classical.choose solved
  have hfix := (Classical.choose_spec solved).1
  have hterminal := (Classical.choose_spec solved).2.1
  have huE := (Classical.choose_spec solved).2.2.1
  have huW := (Classical.choose_spec solved).2.2.2.1
  have herror : ‖u-freeCriticalPath hDensity hSob hfree A R
      (freeEnergyState hDensity hSob (-R) (freeEnergyState hDensity hSob R phi))‖≤eta/2 :=
    (Classical.choose_spec solved).2.2.2.2
  have hefree := congrArg (freeCriticalPath hDensity hSob hfree A R) hcancel
  have herr : ‖u-freeCriticalPath hDensity hSob hfree A R phi‖≤eta/2 :=
    (congrArg (fun v : CriticalPath (intervalMeasure A R) => ‖u-v‖) hefree).symm.le.trans herror
  refine ⟨u,hfix,hterminal,?_,huE,huW,herr⟩
  exact (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hAR
    (energyPath _ u ⟨A,le_rfl,hAR⟩) u).mpr
      (backwardFixedPoint_is_forward_at_initial hDensity hSob h0 hfree hret hH
        hAR (freeEnergyState hDensity hSob R phi) u hfix)

/-- For a fixed terminal cutoff, different left-start constructions agree on
their overlap by actual backward uniqueness. This makes no assertion about
the as-yet-unconstructed limit as the terminal cutoff tends to infinity. -/
theorem terminal_approximations_left_restriction (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel A B R : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hAB : A≤B) (hBR : B≤R) (phi : EnergyState)
    (u : CriticalPath (intervalMeasure A R)) (v : CriticalPath (intervalMeasure B R))
    (hu : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH (hAB.trans hBR)
      (freeEnergyState hDensity hSob R phi) u=u)
    (hv : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hBR
      (freeEnergyState hDensity hSob R phi) v=v) :
    restrictPath hAB hBR le_rfl u=v := by
  have ht := actual_backward_fixedPoint_terminal hDensity hSob h0 hfree hret hH
    (hAB.trans hBR) (freeEnergyState hDensity hSob R phi) u hu
  have hr := restrictPath_backward_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    hAB hBR le_rfl (freeEnergyState hDensity hSob R phi) u hu
  rw [ht] at hr
  exact actual_backward_criticalPath_fixedPoint_unique hDensity hSob h0 hfree hret hH hBR
    (freeEnergyState hDensity hSob R phi) (restrictPath hAB hBR le_rfl u) v hr hv

end HartreeF.WaveTerminal
