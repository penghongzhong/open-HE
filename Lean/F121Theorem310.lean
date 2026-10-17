import FActualFiniteEndpointContinuation
import FActualLeftFiniteEndpointClosure
import FClosedBackwardPathMaximalExtension
import FMaximalFiniteSGlobalScattering

/-! Reconstructed terminal for the manuscript's Theorem 3.10.
All seven conclusions concern the same actual trajectory. Finite-S and pure
gradient bounds are the stated continuation/scattering criteria; neither
continuation, globality, a limiting state, nor scattering is assumed.
The ordinary analytic interfaces remain explicit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121Theorem310
open EnergySpace CriticalPathSpace IntervalTimeTransport MaximalTrajectory
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput
open ForcingDomain FiniteEndpoint MaximalFiniteSGlobal
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace

/-- The seven literal clauses of finite-size continuation and scattering. -/
structure FiniteSizeContinuationAndScattering
    (hDensity : OrdinaryH1Density) {K alpha kernel a : ℝ}
    (hSob : OrdinarySobolev K) {u0 : EnergyState}
    (U : LocalMildTrajectory alpha kernel a u0) : Prop where
  rightGraphBlowup : ∀ (T : ℝ), a < T → Ico a T ⊆ U.domain → T ∉ U.domain →
    ∀ M : ℝ, ¬ UniformCriticalNormBefore U T M
  leftGraphBlowup : ∀ (T c : ℝ), T < c → Ioc T c ⊆ U.domain → T ∉ U.domain →
    ∀ M : ℝ, ¬ UniformCriticalNormAfter U T c M
  rightFiniteSContinuation : ∀ (T G : ℝ), a < T → Ico a T ⊆ U.domain →
    T ∉ U.domain →
    (∀ t ∈ Ico a T, pureGradientNorm (U.state t) ≤ G) →
    FiniteSContinuation.FiniteSBefore U T →
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊂ V.domain ∧ T ∈ V.domain ∧ EqOn V.state U.state U.domain
  leftFiniteSContinuation : ∀ (T G : ℝ), T < a → Ioc T a ⊆ U.domain →
    T ∉ U.domain →
    (∀ t ∈ Ioc T a, pureGradientNorm (U.state t) ≤ G) →
    LeftFiniteSContinuation.FiniteSAfter U T →
    ∃ V : LocalMildTrajectory alpha kernel a u0,
      U.domain ⊂ V.domain ∧ T ∈ V.domain ∧ EqOn V.state U.state U.domain
  rightInfiniteScattering : ∀ G : ℝ, Ici a ⊆ U.domain →
    (∀ t ∈ Ici a, pureGradientNorm (U.state t) ≤ G) →
    ActualScattering.FiniteSAfter U →
    ∃ uPlus : EnergyState,
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uPlus)
        atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0)
  leftInfiniteScattering : ∀ G : ℝ, Iic a ⊆ U.domain →
    (∀ t ∈ Iic a, pureGradientNorm (U.state t) ≤ G) →
    ActualLeftScattering.FiniteSBefore U →
    ∃ uMinus : EnergyState,
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uMinus)
        atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0)
  wholeDomainGlobalScattering : ∀ G : ℝ,
    (∀ t ∈ U.domain, pureGradientNorm (U.state t) ≤ G) → FiniteSOnDomain U →
    U.domain = univ ∧ ∃ uMinus uPlus : EnergyState,
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uMinus)
        atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
      Tendsto (fun t : ℝ => U.state t - freeEnergyState hDensity hSob t uPlus)
        atTop (𝓝 0) ∧
      Tendsto (fun t : ℝ => pureGradientNorm
        (U.state t - freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0)

/-- The complete theorem for any actual maximal representative, keeping the
original datum, actual domain, and trajectory fixed throughout all clauses. -/
theorem theorem310_finite_size_continuation_and_scattering
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel a : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (u0 : EnergyState) (U : LocalMildTrajectory alpha kernel a u0)
    (hmax : U.domain = maximalDomain alpha kernel a u0) :
    FiniteSizeContinuationAndScattering hDensity hSob U := by
  constructor
  · intro T haT hU hT M
    exact maximal_finite_right_endpoint_critical_norm_unbounded
      hDensity hSob h0 hfree hret hefree heret hH u0 U hmax haT hU hT M
  · intro T c hTc hU hT M hbound
    obtain ⟨w, _, hw⟩ := exists_closed_backward_mild_of_uniform_critical_norm
      hDensity hSob h0 hfree hret hH u0 U hTc hU hbound
    obtain ⟨V, _, hTV, _⟩ :=
      closed_backward_mildPath_gives_strict_trajectory_extension
        hDensity hSob h0 hfree hret hefree heret hH hTc.le u0 U
        (hU ⟨hTc, le_rfl⟩) hT w hw
    exact hT (hmax.symm ▸ subset_maximalDomain V hTV)
  · intro T G haT hU hT hgradient hS
    apply FiniteSContinuation.exists_strict_extension_of_finite_s
      hDensity hSob h0 hfree hret hefree heret hH u0 U haT hU hT
      (B := max (K ^ ((6 : ℝ)⁻¹)) 1 * G) _ hS
    intro t ht
    exact (energyState_le_pureGradient hSob (U.state t)).trans
      (mul_le_mul_of_nonneg_left (hgradient t ht)
        (le_trans zero_le_one (le_max_right _ _)))
  · intro T G hTa hU hT hgradient hS
    exact LeftFiniteSContinuation.exists_strict_extension_of_finite_s
      hDensity hSob h0 hfree hret hefree heret hH u0 U hTa hU hT
      (LeftFiniteSContinuation.pure_gradient_actual_state_cap hSob U hgradient) hS
  · intro G hU hgradient hS
    have hG : 0 ≤ G := (pureGradientNorm_nonneg (U.state a)).trans
      (hgradient a Set.self_mem_Ici)
    exact ActualScattering.exists_dotH1_scattering_state_of_finite_s
      hDensity hSob h0 hfree hret hH U hU hG hgradient hS
  · intro G hU hgradient hS
    have hG : 0 ≤ G := (pureGradientNorm_nonneg (U.state a)).trans
      (hgradient a Set.self_mem_Iic)
    exact ActualLeftScattering.exists_dotH1_scattering_state_of_finite_s
      hDensity hSob h0 hfree hret hH U hU hG hgradient hS
  · intro G hgradient hS
    have hglobal : U.domain = univ := maximal_domain_eq_univ_of_finite_s
      hDensity hSob h0 hfree hret hefree heret hH u0 U hmax hgradient hS
    obtain ⟨M, hM⟩ := hS
    obtain ⟨hplus, hminus⟩ := infinite_s_criteria_of_compact_s U M hM
    exact ⟨hglobal, ActualTwoSidedScattering.exists_actual_two_sided_scattering_of_finite_s
      hDensity hSob h0 hfree hret hH U hglobal
      (fun t => hgradient t (hglobal.symm ▸ mem_univ t)) hplus hminus⟩

end HartreeF.Paper121Theorem310
