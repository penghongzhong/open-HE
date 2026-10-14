import FForwardFixedPointDataComparison
import FInitialCompactGeometry
import FTerminalLimitFixedPoint

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveInitialCauchy
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace

attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- Full graph limits preserve the closed energy/gradient caps and their
actual own-initial Hartree fixed-point equation. The displayed comparison
is supplied by the produced small-cap theorem in the final family producer. -/
theorem forward_fixedPoint_of_graph_limit (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B rho a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a≤b)
    (hcompare : ∀ (f g : EnergyState) (u v : CriticalPath (intervalMeasure a b)),
      ‖energyPath _ u‖≤B → ‖energyPath _ v‖≤B →
      ‖fun j => criticalGradient _ j u‖≤rho → ‖fun j => criticalGradient _ j v‖≤rho →
      ‖hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u-
        hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g v‖≤
        max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch*‖f-g‖+(1/2:ℝ)*‖u-v‖)
    (u : ℕ → CriticalPath (intervalMeasure a b)) (v : CriticalPath (intervalMeasure a b))
    (hu : Tendsto u atTop (𝓝 v))
    (hE : ∀ n, ‖energyPath _ (u n)‖≤B)
    (hW : ∀ n, ‖fun j => criticalGradient _ j (u n)‖≤rho)
    (hfix : ∀ n, hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ (u n) ⟨a,le_rfl,hab⟩) (u n)=u n) :
    ‖energyPath _ v‖≤B ∧ ‖fun j => criticalGradient _ j v‖≤rho ∧
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ v ⟨a,le_rfl,hab⟩) v=v := by
  have htE : Tendsto (fun n => energyPath (intervalMeasure a b) (u n)) atTop
      (𝓝 (energyPath (intervalMeasure a b) v)) :=
    ((energyPath (intervalMeasure a b)).continuous.tendsto v).comp hu
  have htEnorm : Tendsto (fun n => ‖energyPath (intervalMeasure a b) (u n)‖) atTop
      (𝓝 ‖energyPath (intervalMeasure a b) v‖) := Filter.Tendsto.norm (E := C(Icc a b, EnergyState)) htE
  have hvE : ‖energyPath _ v‖≤B := le_of_tendsto htEnorm (Eventually.of_forall hE)
  have hcontW : Continuous (fun z : CriticalPath (intervalMeasure a b) =>
      (fun j => criticalGradient _ j z)) := continuous_pi (fun j => (criticalGradient _ j).continuous)
  have htW : Tendsto (fun n => (fun j => criticalGradient (intervalMeasure a b) j (u n)))
      atTop (𝓝 (fun j => criticalGradient (intervalMeasure a b) j v)) :=
    (hcontW.tendsto v).comp hu
  have htWnorm : Tendsto (fun n => ‖fun j => criticalGradient (intervalMeasure a b) j (u n)‖)
      atTop (𝓝 ‖fun j => criticalGradient (intervalMeasure a b) j v‖) := Filter.Tendsto.norm (E := Fin 3 → CriticalGradient (intervalMeasure a b)) htW
  have hvW : ‖fun j => criticalGradient _ j v‖≤rho :=
    le_of_tendsto htWnorm (Eventually.of_forall hW)
  refine ⟨hvE,hvW,?_⟩
  let initial : CriticalPath (intervalMeasure a b) →L[ℂ] EnergyState :=
    (ContinuousMap.evalCLM ℂ ⟨a,le_rfl,hab⟩).comp (energyPath _)
  exact WaveCauchy.fixedPoint_limit_of_two_data_bound
    (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab)
    (max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch) (1/2:ℝ)
    u (fun n => initial (u n)) v (initial v) hu
    ((initial.continuous.tendsto v).comp hu) hfix
    (fun n => hcompare (initial v) (initial (u n)) v (u n) hvE (hE n) hvW (hW n))

/-- Each compact restriction is its actual own-initial solution and retains
both baseline caps. -/
theorem initialCompactSequence_caps_fixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B rho T S : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hrho : 0≤rho) (hST : S≤T) (phi : EnergyState)
    (U : ∀ R : ℝ, R≤T → CriticalPath (intervalMeasure R T))
    (hU : ∀ R (hRT : R≤T), hartreeDuhamelMap hDensity hSob h0 hfree hret hH
      hRT (freeEnergyState hDensity hSob R phi) (U R hRT)=U R hRT)
    (hE : ∀ R (hRT : R≤T), ‖energyPath _ (U R hRT)‖≤B)
    (hW : ∀ R (hRT : R≤T), ‖fun j => criticalGradient _ j (U R hRT)‖≤rho)
    (n : ℕ) :
    let w := initialCompactSequence hST U n
    ‖energyPath _ w‖≤B ∧ ‖fun j => criticalGradient _ j w‖≤rho ∧
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hST
      (energyPath _ w ⟨S,le_rfl,hST⟩) w=w := by
  let R := min S (T-n)
  have hRS : R≤S := min_le_left _ _
  have hRT : R≤T := hRS.trans hST
  let v := U R hRT
  let w := restrictPath hRS hST le_rfl v
  have hwE : ‖energyPath _ w‖≤B :=
    (restrictPath_energy_norm_le hRS hST le_rfl v).trans (hE R hRT)
  have hwW : ‖fun j => criticalGradient _ j w‖≤rho := by
    apply (pi_norm_le_iff_of_nonneg hrho).mpr
    intro j
    exact (restrictPath_gradient_norm_le hRS hST le_rfl v j).trans
      ((norm_le_pi_norm (fun k => criticalGradient _ k v) j).trans (hW R hRT))
  have hfix := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    hRS hST le_rfl (freeEnergyState hDensity hSob R phi) v (hU R hRT)
  have ht := restrictPath_energy hRS hST le_rfl v (⟨S,le_rfl,hST⟩ : Icc S T)
  exact ⟨hwE,hwW,(congrArg (fun f : EnergyState =>
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hST f w) ht).trans hfix⟩

end HartreeF.WaveInitialCauchy
