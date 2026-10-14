import FActualInfiniteLeftSTail
import FSmallSScatteringIncrement

/-! Actual scattering at negative infinite time under finite actual S and
bounded pure dotH1 norm. Time is not reversed in the PDE: all compact mild
paths keep their original orientation, and only the Cauchy filter is dualized. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualLeftScattering
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness CriticalSourceBounds MaximalTrajectory ActualInfiniteLeftSTail
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalPathIntervalSource hartreeDuhamelMap freeCriticalPath freeEnergyState

/-- Genuine finite actual S on the infinite left half-line. -/
def FiniteSBefore {alpha kernel a : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) : Prop :=
  ∃ M : ℝ≥0, UniformSNormBefore U a M

/-- The backward free trajectory is Cauchy along atBot, using actual forward
mild paths on [b,c] with b≤c. No time-reversal solution is postulated. -/
theorem actual_backprop_cauchy_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Iic a ⊆ U.domain) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Iic a, ‖U.state t‖ ≤ B) (hS : FiniteSBefore U) :
    Cauchy (Filter.map (fun t : ℝ => freeEnergyState hDensity hSob (-t) (U.state t)) atBot) := by
  obtain ⟨M, hM⟩ := hS
  let F : ℝᵒᵈ → EnergyState := fun t =>
    freeEnergyState hDensity hSob (-OrderDual.ofDual t) (U.state (OrderDual.ofDual t))
  change CauchySeq F
  apply (Metric.cauchySeq_iff' (β := ℝᵒᵈ) (u := F)).mpr
  intro epsilon hepsilon
  obtain ⟨eta, heta, _, hinc⟩ := ActualScattering.exists_small_s_backprop_increment
    hDensity hSob h0 hfree hret hH hB (half_pos hepsilon)
  obtain ⟨c, hca, htail⟩ := exists_uniform_small_s_left_tail_before
    hDensity hSob U hU M hM heta
  refine ⟨OrderDual.toDual c, ?_⟩
  intro b hbc
  let br : ℝ := OrderDual.ofDual b
  have hbc' : br ≤ c := hbc
  have hI : Set.Icc br c ⊆ U.domain :=
    fun t ht => hU (Set.mem_Iic.mpr (ht.2.trans hca))
  have hE : ‖energyPath (intervalMeasure br c) (U.path hbc' hI)‖ ≤ B := by
    apply (ContinuousMap.norm_le _ hB).mpr
    intro t
    rw [U.path_agrees]
    exact hbound t (Set.mem_Iic.mpr (t.property.2.trans hca))
  have hi := hinc hbc' (U.state br) (U.path hbc' hI) (U.path_mild hbc' hI)
    (hbound br (Set.mem_Iic.mpr (hbc'.trans hca))) hE (htail br hbc' hI).le
  have hd : dist (freeEnergyState hDensity hSob (-br) (U.state br))
      (freeEnergyState hDensity hSob (-c) (U.state c)) ≤ epsilon/2 := by
    rw [dist_eq_norm, norm_sub_rev]
    simpa only [U.path_agrees] using hi
  exact hd.trans_lt (half_lt_self hepsilon)

/-- Completeness constructs the actual incoming state from all real t→−∞. -/
theorem exists_actual_backprop_limit_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Iic a ⊆ U.domain) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Iic a, ‖U.state t‖ ≤ B) (hS : FiniteSBefore U) :
    ∃ uMinus : EnergyState, Tendsto
      (fun t : ℝ => freeEnergyState hDensity hSob (-t) (U.state t)) atBot (𝓝 uMinus) :=
  cauchy_map_iff_exists_tendsto.mp
    (actual_backprop_cauchy_of_finite_s hDensity hSob h0 hfree hret hH U hU hB hbound hS)

/-- The literal free-group identity works for any time filter. -/
theorem pure_gradient_scattering_of_backprop_limit_filter (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (u : ℝ → EnergyState) (uLimit : EnergyState)
    (l : Filter ℝ) (hlim : Tendsto
      (fun t : ℝ => freeEnergyState hDensity hSob (-t) (u t)) l (𝓝 uLimit)) :
    Tendsto (fun t : ℝ => pureGradientNorm (u t - freeEnergyState hDensity hSob t uLimit))
      l (𝓝 0) := by
  have hp := (tendsto_iff_pureGradientNorm_sub hSob).mp hlim
  have he (t : ℝ) : pureGradientNorm (u t - freeEnergyState hDensity hSob t uLimit) =
      pureGradientNorm (freeEnergyState hDensity hSob (-t) (u t) - uLimit) := by
    rw [← freeEnergyState_pureGradientNorm hDensity hSob t
      (freeEnergyState hDensity hSob (-t) (u t) - uLimit),
      freeEnergyState_sub, freeEnergyState_inverse]
  exact hp.congr (fun t => (he t).symm)

/-- The incoming scattering state is produced for the same actual infinite
left-lifespan trajectory, under its genuine finite S and state-norm cap. -/
theorem exists_actual_scattering_state_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a B : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Iic a ⊆ U.domain) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Iic a, ‖U.state t‖ ≤ B) (hS : FiniteSBefore U) :
    ∃ uMinus : EnergyState,
      Tendsto (fun t : ℝ => freeEnergyState hDensity hSob (-t) (U.state t)) atBot (𝓝 uMinus) ∧
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) := by
  obtain ⟨uMinus, hlim⟩ := exists_actual_backprop_limit_of_finite_s
    hDensity hSob h0 hfree hret hH U hU hB hbound hS
  have hp := pure_gradient_scattering_of_backprop_limit_filter hDensity hSob U.state uMinus atBot hlim
  refine ⟨uMinus, hlim, ?_, hp⟩
  apply (tendsto_iff_pureGradientNorm_sub hSob).mpr
  simpa only [sub_zero] using hp

/-- Incoming scattering in the original homogeneous norm; the L6/state cap
is derived from the pure gradient cap using the proved Sobolev comparison. -/
theorem exists_dotH1_scattering_state_of_finite_s (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel a G : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    {u0 : EnergyState} (U : LocalMildTrajectory alpha kernel a u0)
    (hU : Set.Iic a ⊆ U.domain) (hG : 0 ≤ G)
    (hbound : ∀ t ∈ Set.Iic a, pureGradientNorm (U.state t) ≤ G)
    (hS : FiniteSBefore U) :
    ∃ uMinus : EnergyState,
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) := by
  let C : ℝ := max (K ^ ((6 : ℝ)⁻¹)) 1
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hstate : ∀ t ∈ Set.Iic a, ‖U.state t‖ ≤ C*G := by
    intro t ht
    exact (energyState_le_pureGradient hSob (U.state t)).trans
      (mul_le_mul_of_nonneg_left (hbound t ht) hC)
  obtain ⟨uMinus, _, he, hg⟩ := exists_actual_scattering_state_of_finite_s
    hDensity hSob h0 hfree hret hH U hU (mul_nonneg hC hG) hstate hS
  exact ⟨uMinus, he, hg⟩

set_option pp.universes true
#check @FiniteSBefore
#print axioms FiniteSBefore
#check @actual_backprop_cauchy_of_finite_s
#print axioms actual_backprop_cauchy_of_finite_s
#check @exists_actual_backprop_limit_of_finite_s
#print axioms exists_actual_backprop_limit_of_finite_s
#check @pure_gradient_scattering_of_backprop_limit_filter
#print axioms pure_gradient_scattering_of_backprop_limit_filter
#check @exists_actual_scattering_state_of_finite_s
#print axioms exists_actual_scattering_state_of_finite_s
#check @exists_dotH1_scattering_state_of_finite_s
#print axioms exists_dotH1_scattering_state_of_finite_s
end HartreeF.ActualLeftScattering
