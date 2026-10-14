import FCompactLimitPrescribedAsymptote
import FCompactLimitCompatibility

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveRealization
open EnergySpace CriticalPathSpace CriticalPathRestriction CriticalUniqueness MaximalTrajectory
open ActualDuhamelPath IntervalTimeTransport SobolevStretch StationarySelfTest Retarded
open ActualStrichartz ForcingDomain EndpointOutput WaveCauchy
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath restrictPath
  IsMildHartreePath backwardHartreeDuhamelMap criticalPathIntervalSource freeCriticalPath

/-- Positive-time wave operator for arbitrary homogeneous asymptotic data.
The same ACTUAL canonical maximal trajectory covers every future time and
has the prescribed strong EnergyState asymptote. Uniform compact E/W caps
and literal mild paths are outputs. No compatible-family, half-line norm,
initial scalar-L2, global-existence or prior-scattering premise is supplied. -/
theorem exists_positive_actual_wave_operator (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) :
    ∃ B rho T : ℝ, ∃ f : EnergyState, 0<B ∧ 0<rho ∧ rho≤1 ∧
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
      Ici T ⊆ M.domain ∧
      Tendsto (fun t => ‖M.state t-freeEnergyState hDensity hSob t phi‖) atTop (𝓝 0) ∧
      ∀ S (hTS : T≤S), ∃ u : CriticalPath (intervalMeasure T S),
        (∀ t : Icc T S, M.state t=energyPath _ u t) ∧
        IsMildHartreePath hTS alpha kernel f u ∧
        ‖energyPath _ u‖≤B ∧ ‖fun j => criticalGradient _ j u‖≤rho := by
  let produced := exists_positive_terminal_cauchy_family hDensity hSob h0 hfree hret hH phi
  let B : ℝ := Classical.choose produced
  let radius := Classical.choose_spec produced
  let rho : ℝ := Classical.choose radius
  let time := Classical.choose_spec radius
  let T : ℝ := Classical.choose time
  have hB : 0<B := (Classical.choose_spec time).1
  have hrho : 0<rho := (Classical.choose_spec time).2.1
  have hrho1 : rho≤1 := (Classical.choose_spec time).2.2.1
  let family := (Classical.choose_spec time).2.2.2
  let U : ∀ R : ℝ, T≤R → CriticalPath (intervalMeasure T R) := Classical.choose family
  let limits := (Classical.choose_spec family).2.2.2.2.1
  let V : ∀ S : ℝ, T≤S → CriticalPath (intervalMeasure T S) :=
    fun S hTS => Classical.choose (limits S hTS)
  have hV : ∀ S (hTS : T≤S), Tendsto (terminalCompactSequence hTS U) atTop (𝓝 (V S hTS)) := by
    intro S hTS
    exact (Classical.choose_spec (limits S hTS)).1
  have hcompatible : ∀ S R (hTS : T≤S) (hSR : S≤R),
      restrictPath le_rfl hTS hSR (V R (hTS.trans hSR))=V S hTS := by
    intro S R hTS hSR
    exact terminalCompactLimits_compatible hTS hSR U (V S hTS) (V R (hTS.trans hSR))
      (hV S hTS) (hV R (hTS.trans hSR))
  have hmild : ∀ S (hTS : T≤S), IsMildHartreePath hTS alpha kernel
      (energyPath _ (V S hTS) ⟨T,le_rfl,hTS⟩) (V S hTS) := by
    intro S hTS
    exact (Classical.choose_spec (limits S hTS)).2.2.2.2
  have hmax := compatibleCompactLimits_maximal hDensity hSob h0 hfree hret hefree heret hH
    V hcompatible hmild
  let f := compactLimitDatum V
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
  have hdomain : Ici T ⊆ M.domain := hmax.1
  have hstate : ∀ S (hTS : T≤S) (t : Icc T S), M.state t=energyPath _ (V S hTS) t := hmax.2
  have hlate : ∀ delta : ℝ, 0<delta → ∃ A : ℝ, ∃ hTA : T≤A,
      ∀ R (hAR : A≤R), ‖restrictPath hTA hAR le_rfl (U R (hTA.trans hAR))-
        freeCriticalPath hDensity hSob hfree A R phi‖≤delta/2 := by
    intro delta hdelta
    let late := (Classical.choose_spec family).2.2.2.2.2 delta hdelta
    let A : ℝ := Classical.choose late
    let hTA : T≤A := Classical.choose (Classical.choose_spec late)
    refine ⟨A,hTA,?_⟩
    intro R hAR
    exact (Classical.choose_spec (Classical.choose_spec late) R hAR).2.2
  have hasymptote := compactLimits_state_prescribed_asymptote hDensity hSob hfree phi U V hV hlate
    M.state hstate
  refine ⟨B,rho,T,f,hB,hrho,hrho1,hdomain,hasymptote,?_⟩
  intro S hTS
  have hi := compatibleCompactLimits_initial V hcompatible S hTS
  have hm : IsMildHartreePath hTS alpha kernel (compactLimitDatum V) (V S hTS) :=
    hi ▸ hmild S hTS
  refine ⟨V S hTS,hstate S hTS,hm,?_,?_⟩
  · exact (Classical.choose_spec (limits S hTS)).2.1
  · exact (Classical.choose_spec (limits S hTS)).2.2.1

end HartreeF.WaveRealization
