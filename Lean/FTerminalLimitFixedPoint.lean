import FBackwardFixedPointDataComparison
import FTerminalCompactGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveCauchy
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace

/-- A two-data bound closes actual fixed points without a separate nonlinear
continuity oracle. This elementary lemma is instantiated below in the genuine
critical graph with its native Hartree estimate. -/
theorem fixedPoint_limit_of_two_data_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : F → E → E) (L q : ℝ) (u : ℕ → E) (f : ℕ → F) (v : E) (g : F)
    (hu : Tendsto u atTop (𝓝 v)) (hf : Tendsto f atTop (𝓝 g))
    (hfix : ∀ n, P (f n) (u n)=u n)
    (hbound : ∀ n, ‖P g v-P (f n) (u n)‖≤L*‖g-f n‖+q*‖v-u n‖) : P g v=v := by
  have hle : ∀ n, ‖P g v-v‖≤L*‖g-f n‖+(q+1)*‖v-u n‖ := by
    intro n
    have ht : ‖P g v-v‖≤‖P g v-P (f n) (u n)‖+‖P (f n) (u n)-v‖ := by
      simpa only [sub_add_sub_cancel] using
        (norm_add_le (P g v-P (f n) (u n)) (P (f n) (u n)-v))
    rw [hfix n, norm_sub_rev (u n) v] at ht
    have hb := hbound n
    rw [hfix n] at hb
    nlinarith only [ht,hb]
  have hzero : Tendsto (fun n => L*‖g-f n‖+(q+1)*‖v-u n‖) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub hf).norm).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hu).norm) using 1
    simp
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto hzero
    (Eventually.of_forall hle)) (norm_nonneg _)))

attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  freeCriticalPath backwardHartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- Full graph limits preserve the closed energy/gradient caps and their
actual own-terminal Hartree fixed-point equation. The displayed comparison
is supplied by the produced small-cap theorem in the final family producer. -/
theorem backward_fixedPoint_of_graph_limit (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B rho a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hab : a≤b)
    (hcompare : ∀ (f g : EnergyState) (u v : CriticalPath (intervalMeasure a b)),
      ‖energyPath _ u‖≤B → ‖energyPath _ v‖≤B →
      ‖fun j => criticalGradient _ j u‖≤rho → ‖fun j => criticalGradient _ j v‖≤rho →
      ‖backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u-
        backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g v‖≤
        max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch*‖f-g‖+(1/2:ℝ)*‖u-v‖)
    (u : ℕ → CriticalPath (intervalMeasure a b)) (v : CriticalPath (intervalMeasure a b))
    (hu : Tendsto u atTop (𝓝 v))
    (hE : ∀ n, ‖energyPath _ (u n)‖≤B)
    (hW : ∀ n, ‖fun j => criticalGradient _ j (u n)‖≤rho)
    (hfix : ∀ n, backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ (u n) ⟨b,hab,le_rfl⟩) (u n)=u n) :
    ‖energyPath _ v‖≤B ∧ ‖fun j => criticalGradient _ j v‖≤rho ∧
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ v ⟨b,hab,le_rfl⟩) v=v := by
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
  let terminal : CriticalPath (intervalMeasure a b) →L[ℂ] EnergyState :=
    (ContinuousMap.evalCLM ℂ ⟨b,hab,le_rfl⟩).comp (energyPath _)
  exact fixedPoint_limit_of_two_data_bound
    (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab)
    (max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch) (1/2:ℝ)
    u (fun n => terminal (u n)) v (terminal v) hu
    ((terminal.continuous.tendsto v).comp hu) hfix
    (fun n => hcompare (terminal v) (terminal (u n)) v (u n) hvE (hE n) hvW (hW n))

/-- Every term of the common compact sequence is the actual own-terminal
solution on that compact interval, and retains the baseline caps. -/
theorem terminalCompactSequence_caps_fixedPoint (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B rho T S : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hrho : 0≤rho) (hTS : T≤S) (phi : EnergyState)
    (U : ∀ R : ℝ, T≤R → CriticalPath (intervalMeasure T R))
    (hU : ∀ R (hTR : T≤R), backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH
      hTR (freeEnergyState hDensity hSob R phi) (U R hTR)=U R hTR)
    (hE : ∀ R (hTR : T≤R), ‖energyPath _ (U R hTR)‖≤B)
    (hW : ∀ R (hTR : T≤R), ‖fun j => criticalGradient _ j (U R hTR)‖≤rho)
    (n : ℕ) :
    let w := terminalCompactSequence hTS U n
    ‖energyPath _ w‖≤B ∧ ‖fun j => criticalGradient _ j w‖≤rho ∧
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hTS
      (energyPath _ w ⟨S,hTS,le_rfl⟩) w=w := by
  let R := max S (T+n)
  have hSR : S≤R := le_max_left _ _
  have hTR : T≤R := hTS.trans hSR
  let v := U R hTR
  let w := restrictPath le_rfl hTS hSR v
  have hwE : ‖energyPath _ w‖≤B :=
    (restrictPath_energy_norm_le le_rfl hTS hSR v).trans (hE R hTR)
  have hwW : ‖fun j => criticalGradient _ j w‖≤rho := by
    apply (pi_norm_le_iff_of_nonneg hrho).mpr
    intro j
    exact (restrictPath_gradient_norm_le le_rfl hTS hSR v j).trans
      ((norm_le_pi_norm (fun k => criticalGradient _ k v) j).trans (hW R hTR))
  have hfix := restrictPath_backward_hartree_fixedPoint hDensity hSob h0 hfree hret hH
    le_rfl hTS hSR (freeEnergyState hDensity hSob R phi) v (hU R hTR)
  have ht := restrictPath_energy le_rfl hTS hSR v (⟨S,hTS,le_rfl⟩ : Icc T S)
  exact ⟨hwE,hwW,(congrArg (fun f : EnergyState =>
    backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hTS f w) ht).trans hfix⟩

end HartreeF.WaveCauchy
