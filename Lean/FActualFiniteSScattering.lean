import FSmallSScatteringIncrement
import FActualInfiniteSTail

/-! The actual finite-S scattering criterion on an infinite forward lifespan.
The source tails, Cauchy property, and limiting state are produced. The genuine
finite S hypothesis and bounded homogeneous-energy norm remain explicit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualScattering
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness CriticalSourceBounds SmallSGraphBound MaximalTrajectory ActualSTail
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalPathIntervalSource hartreeDuhamelMap freeCriticalPath freeEnergyState

/-- Finiteness refers to the actual compact-prefix S norms of this trajectory. -/
def FiniteSAfter {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) : Prop :=
  ∃ M : ℝ≥0, UniformSNormAfter U a M

/-- The actual backward free orbit is Cauchy. One genuine S-tail cutoff
works for every later endpoint; neither a source-tail bound nor a limiting
state is supplied as a premise. -/
theorem actual_backprop_cauchy_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Ici a ⊆ U.domain) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Ici a, ‖U.state t‖ ≤ B) (hS : FiniteSAfter U) :
    CauchySeq (fun t : ℝ => freeEnergyState hDensity hSob (-t) (U.state t)) := by
  obtain ⟨M, hM⟩ := hS
  apply Metric.cauchySeq_iff'.mpr
  intro epsilon hepsilon
  obtain ⟨eta, heta, _, hinc⟩ := exists_small_s_backprop_increment
    hDensity hSob h0 hfree hret hH hB (half_pos hepsilon)
  obtain ⟨c, hac, htail⟩ := exists_uniform_small_s_tail_after
    hDensity hSob U hU M hM heta
  refine ⟨c, ?_⟩
  intro b hcb
  have hI : Set.Icc c b ⊆ U.domain := fun t ht => hU (hac.trans ht.1)
  have hE : ‖energyPath (intervalMeasure c b) (U.path hcb hI)‖ ≤ B := by
    apply (ContinuousMap.norm_le _ hB).mpr
    intro t
    rw [U.path_agrees]
    exact hbound t (hac.trans t.property.1)
  have hb := hinc hcb (U.state c) (U.path hcb hI) (U.path_mild hcb hI)
    (hbound c hac) hE (htail b hcb hI).le
  have hd : dist (freeEnergyState hDensity hSob (-b) (U.state b))
      (freeEnergyState hDensity hSob (-c) (U.state c)) ≤ epsilon/2 := by
    simpa only [dist_eq_norm, U.path_agrees] using hb
  exact hd.trans_lt (half_lt_self hepsilon)

/-- A real limiting state is constructed using the completeness of the
existing EnergyState. The convergence is over all real t→+∞. -/
theorem exists_actual_backprop_limit_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Ici a ⊆ U.domain) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Ici a, ‖U.state t‖ ≤ B) (hS : FiniteSAfter U) :
    ∃ uPlus : EnergyState, Tendsto
      (fun t : ℝ => freeEnergyState hDensity hSob (-t) (U.state t)) atTop (𝓝 uPlus) :=
  cauchySeq_tendsto_of_complete
    (actual_backprop_cauchy_of_finite_s hDensity hSob h0 hfree hret hH U hU hB hbound hS)

/-- The literal full Fourier group converts a constructed backward free limit
to convergence in the genuine homogeneous gradient norm. -/
theorem pure_gradient_scattering_of_backprop_limit (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : ℝ → EnergyState) (uPlus : EnergyState)
    (hlim : Tendsto (fun t : ℝ => freeEnergyState hDensity hSob (-t) (u t))
      atTop (𝓝 uPlus)) :
    Tendsto (fun t : ℝ => pureGradientNorm (u t - freeEnergyState hDensity hSob t uPlus))
      atTop (𝓝 0) := by
  have hp := (tendsto_iff_pureGradientNorm_sub hSob).mp hlim
  have he (t : ℝ) : pureGradientNorm (u t - freeEnergyState hDensity hSob t uPlus) =
      pureGradientNorm (freeEnergyState hDensity hSob (-t) (u t) - uPlus) := by
    rw [← freeEnergyState_pureGradientNorm hDensity hSob t
      (freeEnergyState hDensity hSob (-t) (u t) - uPlus),
      freeEnergyState_sub, freeEnergyState_inverse]
  exact hp.congr (fun t => (he t).symm)

/-- Genuine finite S and a uniform actual-state cap produce an actual
scattering state in both the full energy topology and the pure gradient norm.
This is a criterion on an already infinite actual lifespan. -/
theorem exists_actual_scattering_state_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Ici a ⊆ U.domain) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Ici a, ‖U.state t‖ ≤ B) (hS : FiniteSAfter U) :
    ∃ uPlus : EnergyState,
      Tendsto (fun t : ℝ => freeEnergyState hDensity hSob (-t) (U.state t)) atTop (𝓝 uPlus) ∧
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) := by
  obtain ⟨uPlus, hlim⟩ := exists_actual_backprop_limit_of_finite_s
    hDensity hSob h0 hfree hret hH U hU hB hbound hS
  have hp := pure_gradient_scattering_of_backprop_limit hDensity hSob U.state uPlus hlim
  refine ⟨uPlus, hlim, ?_, hp⟩
  apply (tendsto_iff_pureGradientNorm_sub hSob).mpr
  simpa only [sub_zero] using hp

/-- The criterion in the original homogeneous gradient norm. The L6
coordinate cap is derived from Sobolev, not supplied as an extra condition. -/
theorem exists_dotH1_scattering_state_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a G : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Ici a ⊆ U.domain) (hG : 0 ≤ G)
    (hbound : ∀ t ∈ Set.Ici a, pureGradientNorm (U.state t) ≤ G)
    (hS : FiniteSAfter U) :
    ∃ uPlus : EnergyState,
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) := by
  let C : ℝ := max (K ^ ((6 : ℝ)⁻¹)) 1
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hstate : ∀ t ∈ Set.Ici a, ‖U.state t‖ ≤ C*G := by
    intro t ht
    exact (energyState_le_pureGradient hSob (U.state t)).trans
      (mul_le_mul_of_nonneg_left (hbound t ht) hC)
  obtain ⟨uPlus, _, he, hg⟩ := exists_actual_scattering_state_of_finite_s
    hDensity hSob h0 hfree hret hH U hU (mul_nonneg hC hG) hstate hS
  exact ⟨uPlus, he, hg⟩

set_option pp.universes true
#check @FiniteSAfter
#print axioms FiniteSAfter
#check @actual_backprop_cauchy_of_finite_s
#print axioms actual_backprop_cauchy_of_finite_s
#check @exists_actual_backprop_limit_of_finite_s
#print axioms exists_actual_backprop_limit_of_finite_s
#check @pure_gradient_scattering_of_backprop_limit
#print axioms pure_gradient_scattering_of_backprop_limit
#check @exists_actual_scattering_state_of_finite_s
#print axioms exists_actual_scattering_state_of_finite_s
#check @exists_dotH1_scattering_state_of_finite_s
#print axioms exists_dotH1_scattering_state_of_finite_s
end HartreeF.ActualScattering
