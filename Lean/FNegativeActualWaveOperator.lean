import FInitialCompactLimitPrescribedAsymptote
import FInitialCompactLimitCompatibility

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.IncomingWaveRealization
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalUniqueness MaximalTrajectory
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest Retarded
open ActualStrichartz ForcingDomain EndpointOutput WaveInitialCauchy
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath
  IsMildHartreePath IsBackwardMildHartreePath hartreeDuhamelMap backwardHartreeDuhamelMap
  criticalPathIntervalSource freeCriticalPath

/-- The actual incoming wave trajectory is produced for every original
homogeneous phi at a phi-dependent marked time T. The SAME canonical maximal
trajectory covers the full past half-line and has the prescribed strong
EnergyState asymptote. Compatibility, common right trace and all genuine
compact mild paths are produced, without a symmetry or global-norm premise. -/
theorem exists_negative_actual_wave_operator (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) :
    ∃ B rho T : ℝ, ∃ f : EnergyState, 0<B ∧ 0<rho ∧ rho≤1 ∧
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
      Iic T ⊆ M.domain ∧
      Tendsto (fun t => ‖M.state t-freeEnergyState hDensity hSob t phi‖) atBot (𝓝 0) ∧
      ∀ S (hST : S≤T), ∃ u : CriticalPath (intervalMeasure S T),
        (∀ t : Icc S T, M.state t=energyPath _ u t) ∧
        IsBackwardMildHartreePath hST alpha kernel f u ∧
        IsMildHartreePath hST alpha kernel (energyPath _ u ⟨S,le_rfl,hST⟩) u ∧
        ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤rho := by
  let produced := exists_negative_initial_cauchy_family hDensity hSob h0 hfree hret hH phi
  let B : ℝ := Classical.choose produced
  let radius := Classical.choose_spec produced
  let rho : ℝ := Classical.choose radius
  let time := Classical.choose_spec radius
  let T : ℝ := Classical.choose time
  have hB : 0<B := (Classical.choose_spec time).1
  have hrho : 0<rho := (Classical.choose_spec time).2.1
  have hrho1 : rho≤1 := (Classical.choose_spec time).2.2.1
  let family := (Classical.choose_spec time).2.2.2
  let U : ∀ R : ℝ, R≤T → CriticalPath (intervalMeasure R T) := Classical.choose family
  let limits := (Classical.choose_spec family).2.2.2.2.1
  let V : ∀ S : ℝ, S≤T → CriticalPath (intervalMeasure S T) :=
    fun S hST => Classical.choose (limits S hST)
  have hV : ∀ S (hST : S≤T), Tendsto (initialCompactSequence hST U) atTop (𝓝 (V S hST)) := by
    intro S hST
    exact (Classical.choose_spec (limits S hST)).1
  have hcompatible : ∀ S R (hST : S≤T) (hRS : R≤S),
      restrictPath hRS hST le_rfl (V R (hRS.trans hST))=V S hST := by
    intro S R hST hRS
    exact initialCompactLimits_compatible hST hRS U (V S hST) (V R (hRS.trans hST))
      (hV S hST) (hV R (hRS.trans hST))
  have hmild : ∀ S (hST : S≤T), IsMildHartreePath hST alpha kernel
      (energyPath _ (V S hST) ⟨S,le_rfl,hST⟩) (V S hST) := by
    intro S hST
    exact (Classical.choose_spec (limits S hST)).2.2.2.2
  have hbmild : ∀ S (hST : S≤T), IsBackwardMildHartreePath hST alpha kernel
      (energyPath _ (V S hST) ⟨T,hST,le_rfl⟩) (V S hST) := by
    intro S hST
    apply (isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hST
      (energyPath _ (V S hST) ⟨T,hST,le_rfl⟩) (V S hST)).mpr
    exact forwardFixedPoint_is_backward_at_terminal hDensity hSob h0 hfree hret hH hST
      (energyPath _ (V S hST) ⟨S,le_rfl,hST⟩) (V S hST)
      (Classical.choose_spec (limits S hST)).2.2.2.1
  have hmax := compatibleInitialCompactLimits_maximal hDensity hSob h0 hfree hret hefree heret hH
    V hcompatible hbmild
  let f := incomingCompactLimitDatum V
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
  have hdomain : Iic T ⊆ M.domain := hmax.1
  have hstate : ∀ S (hST : S≤T) (t : Icc S T), M.state t=energyPath _ (V S hST) t := hmax.2
  have hearly : ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hAT : A≤T,
      ∀ R (hRA : R≤A), ‖restrictPath le_rfl hRA hAT (U R (hRA.trans hAT))-
        freeCriticalPath hDensity hSob hfree R A phi‖≤delta/2 := by
    intro delta hdelta
    let early := (Classical.choose_spec family).2.2.2.2.2 delta hdelta
    let A : ℝ := Classical.choose early
    let hAT : A≤T := Classical.choose (Classical.choose_spec early)
    refine ⟨A,hAT,?_⟩
    intro R hRA
    exact (Classical.choose_spec (Classical.choose_spec early) R hRA).2.2
  have hasymptote := initialCompactLimits_state_prescribed_asymptote hDensity hSob hfree phi U V hV hearly
    M.state hstate
  refine ⟨B,rho,T,f,hB,hrho,hrho1,hdomain,hasymptote,?_⟩
  intro S hST
  have hi := compatibleInitialCompactLimits_terminal V hcompatible S hST
  have hbm : IsBackwardMildHartreePath hST alpha kernel (incomingCompactLimitDatum V) (V S hST) :=
    hi ▸ hbmild S hST
  refine ⟨V S hST,hstate S hST,hbm,hmild S hST,?_,?_⟩
  · exact (Classical.choose_spec (limits S hST)).2.1
  · exact (Classical.choose_spec (limits S hST)).2.2.1

end HartreeF.IncomingWaveRealization
