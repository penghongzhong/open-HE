import FCompactUniformCenteredLifespanNative
import FMaximalAffineDomain
import FCriticalAffineL2Continuity
import Mathlib.Topology.Order.Monotone

/-! Native maximal-domain windows and finite-endpoint scale collapse.
AUTHOR CANDIDATE, NOT COMPILED. This supplies the lifespan/collapse producer,
not an input asserting finite-endpoint exclusion. No original value L2 occurs. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open Set Filter
open scoped Topology
namespace HartreeF.NativeCompactScale
open EnergySpace SobolevStretch StationarySelfTest Retarded ActualStrichartz
open EndpointOutput ForcingDomain MaximalTrajectory MaximalAffine
open CriticalAffine AffineMixed CompactUniformLifespan

/-- Only the marked datum is changed; all actual states and finite mild paths
are retained. This is the same elementary record construction as the existing
FSmallSTailContinuation recenterWithDatum, without its unrelated imports. -/
def remark {alpha kernel s : ℝ} {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (t : ℝ) (g : EnergyState)
    (ht : t ∈ U.domain) (he : U.state t = g) :
    LocalMildTrajectory alpha kernel t g where
  domain := U.domain
  state := U.state
  domain_open := U.domain_open
  domain_connected := U.domain_connected
  center_mem := ht
  continuous := U.continuous
  initial := he
  compact := U.compact

/-- Maximality on the actual solution family gives exact recentering of its
native domain. No globality or continuation criterion is assumed. -/
theorem actual_domain_remark (hD : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s : ℝ}
    (hS : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (f : EnergyState) {t : ℝ}
    (ht : t ∈ (actualMaximalTrajectory hD hS h0 hfree hret hefree heret hH s f).domain) :
    maximalDomain alpha kernel t
      ((actualMaximalTrajectory hD hS h0 hfree hret hefree heret hH s f).state t) =
      (actualMaximalTrajectory hD hS h0 hfree hret hefree heret hH s f).domain := by
  let M := actualMaximalTrajectory hD hS h0 hfree hret hefree heret hH s f
  let N := actualMaximalTrajectory hD hS h0 hfree hret hefree heret hH t (M.state t)
  let R := remark M t (M.state t) ht rfl
  have hMN : M.domain ⊆ N.domain := subset_maximalDomain R
  have hsN : s ∈ N.domain := hMN M.center_mem
  have hs : N.state s = f :=
    (LocalMildTrajectory.overlap_eq hD hS h0 hfree hret hH N R hsN M.center_mem).trans
      M.initial
  let W := remark N s f hsN hs
  have hNM : N.domain ⊆ M.domain := subset_maximalDomain W
  exact Set.Subset.antisymm hNM hMN

/-- One lifespan window works for every normalization in the genuine compact
carrier. Spatial covariance and maximality put the whole parabolic window
back into the original actual maximal domain. -/
theorem exists_actual_compact_normalized_window (hD : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ}
    (hS : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    {Q : Set EnergyState} (hQ : IsCompact Q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (s : ℝ) (f : EnergyState) (t : ℝ),
      let M := actualMaximalTrajectory hD hS h0 hfree hret hefree heret hH s f
      t ∈ M.domain → ∀ (ρ : ℝ) (hρ : 0 < ρ) (y : Space),
      (criticalAffineState ρ hρ y).symm (M.state t) ∈ Q →
      ∀ τ ∈ Icc (-δ) δ, t + ρ ^ 2 * τ ∈ M.domain := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_compact_uniform_centered_lifespan
    hD hS h0 hfree hret hH hQ
  refine ⟨δ, hδ, ?_⟩
  intro s f t M ht ρ hρ y hq τ hτ
  let q := (criticalAffineState ρ hρ y).symm (M.state t)
  obtain ⟨V, hV⟩ := hlocal q hq
  have heq : q = affineState hρ y (M.state t) :=
    criticalAffineState_symm_eq_affineState ρ hρ y (M.state t)
  have hm : τ ∈ maximalDomain alpha kernel 0 (affineState hρ y (M.state t)) := by
    rw [← heq]
    exact subset_maximalDomain V (hV hτ)
  have hdom : maximalDomain alpha kernel 0 (affineState hρ y (M.state t)) =
      (timeAffine ρ t) ⁻¹' maximalDomain alpha kernel t (M.state t) := by
    simpa only [timeAffine, mul_zero, zero_add] using
      maximalDomain_affine hD hS h0 hfree hret hH hρ y t 0 (M.state t)
  rw [hdom] at hm
  have hback : t + ρ ^ 2 * τ ∈ maximalDomain alpha kernel t (M.state t) := by
    simpa only [mem_preimage, timeAffine, add_comm] using hm
  rw [actual_domain_remark hD hS h0 hfree hret hefree heret hH f ht] at hback
  exact hback

/-- A genuine right parabolic domain window forces physical scale collapse.
All hypotheses concern S only; no outside-domain positivity is imposed. -/
theorem scale_tendsto_zero_at_right_endpoint {S : Set ℝ} {T δ : ℝ}
    (hδ : 0 < δ) (hbefore : ∀ t ∈ S, t < T) (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ S, 0 < ρ t)
    (hwindow : ∀ t ∈ S, t + δ * ρ t ^ 2 ∈ S) :
    Tendsto ρ (𝓝[S] T) (𝓝 0) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[S] T) (𝓝 T) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hgap : Tendsto (fun t : ℝ => T - t) (𝓝[S] T) (𝓝 0) := by
    simpa only [sub_self] using hid.const_sub T
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < δ * ε ^ 2 := mul_pos hδ (sq_pos_of_pos hε)
  filter_upwards [self_mem_nhdsWithin, hgap.eventually_lt_const he] with t ht hsmall
  have hbound := hbefore (t + δ * ρ t ^ 2) (hwindow t ht)
  have hpos := hρ t ht
  have hsq : ρ t ^ 2 < ε ^ 2 := (mul_lt_mul_iff_right₀ hδ).mp (by linarith)
  have hlt : ρ t < ε := by nlinarith
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hpos] using hlt

/-- The left endpoint uses the left actual window, without a time-reflection
identity for the Hartree equation. -/
theorem scale_tendsto_zero_at_left_endpoint {S : Set ℝ} {T δ : ℝ}
    (hδ : 0 < δ) (hafter : ∀ t ∈ S, T < t) (ρ : ℝ → ℝ)
    (hρ : ∀ t ∈ S, 0 < ρ t)
    (hwindow : ∀ t ∈ S, t - δ * ρ t ^ 2 ∈ S) :
    Tendsto ρ (𝓝[S] T) (𝓝 0) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[S] T) (𝓝 T) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hgap : Tendsto (fun t : ℝ => t - T) (𝓝[S] T) (𝓝 0) := by
    simpa only [sub_self] using hid.sub_const T
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < δ * ε ^ 2 := mul_pos hδ (sq_pos_of_pos hε)
  filter_upwards [self_mem_nhdsWithin, hgap.eventually_lt_const he] with t ht hsmall
  have hbound := hafter (t - δ * ρ t ^ 2) (hwindow t ht)
  have hpos := hρ t ht
  have hsq : ρ t ^ 2 < ε ^ 2 := (mul_lt_mul_iff_right₀ hδ).mp (by linarith)
  have hlt : ρ t < ε := by nlinarith
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hpos] using hlt

end HartreeF.NativeCompactScale
