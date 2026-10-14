import FActualNonlinearProfileProducer
import FCommonLinearProfileTimeNormalization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open Filter
open scoped Topology BigOperators

namespace HartreeF.CountableNonlinearProfiles
open EnergySpace SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput
open MaximalTrajectory NonlinearProfile ProfileEnergy CommonProfileTimes ForcingDomain

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)

/-- A single countable family of actual canonical maximal Hartree trajectories.
Every label uses its actual profile and its actual time sequence. The eventual
membership prevents interpreting totalized values outside the maximal domain
as nonlinear evolution. No extra extraction occurs in this predicate. -/
def ActualProfileFamilyApproximation (P : LinearProfileFamily)
    (T : ℕ → ℝ) (f : ℕ → EnergyState) : Prop :=
  ∀ j : ℕ,
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH (T j) (f j)
    (∀ᶠ n in atTop, P.time j n ∈ M.domain) ∧
      Tendsto (fun n => ‖M.state (P.time j n) -
        freeEnergyState hDensity hSob (P.time j n) (P.profile j)‖) atTop (𝓝 0)

/-- The simultaneous statement is only for each fixed finite set of labels.
There is no uniform-in-label or infinite-sum claim. -/
def FiniteProfileControl (P : LinearProfileFamily) (T : ℕ → ℝ)
    (f : ℕ → EnergyState) (J : Finset ℕ) : Prop :=
  let M := fun j => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
    (T j) (f j)
  (∀ᶠ n in atTop, ∀ j ∈ J, P.time j n ∈ (M j).domain) ∧
    Tendsto (fun n => ∑ j ∈ J, ‖(M j).state (P.time j n) -
      freeEnergyState hDensity hSob (P.time j n) (P.profile j)‖) atTop (𝓝 0)

/-- Countable choice is applied to the already proved actual finite/positive-
infinite/negative-infinite producer. Thus the finite branch keeps the original
anchor (sstar, U(sstar) phi). The supplied time sequence is unchanged for every
label, and one pair of anchor/data functions works for all labels at once. -/
theorem exists_countable_actual_nonlinear_profiles (P : LinearProfileFamily)
    (ht : ∀ j : ℕ, TimeRegime (P.time j)) :
    ∃ T : ℕ → ℝ, ∃ f : ℕ → EnergyState,
      ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hH P T f := by
  choose T f hf using fun j => exists_actual_nonlinear_profile
    hDensity hSob h0 hfree hret hefree heret hH (P.profile j) (P.time j) (ht j)
  exact ⟨T, f, hf⟩

/-- Finite intersection of eventual true-domain membership and continuity of
finite sums give simultaneous control, with no new analytic premise. -/
theorem finite_profile_control {P : LinearProfileFamily} {T : ℕ → ℝ}
    {f : ℕ → EnergyState}
    (hA : ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hH P T f)
    (J : Finset ℕ) :
    FiniteProfileControl hDensity hSob h0 hfree hret hefree heret hH P T f J := by
  refine ⟨(eventually_all_finset J).2 (fun j _ => (hA j).1), ?_⟩
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum J (fun j _ => (hA j).2)

/-- For any fixed finite set and positive tolerance, one integer threshold
ensures both true-domain membership for every selected label and small total
error. This does not compare nonlinear profiles in spacetime. -/
theorem finite_profile_eventual_bound {P : LinearProfileFamily} {T : ℕ → ℝ}
    {f : ℕ → EnergyState}
    (hA : ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hH P T f)
    (J : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := fun j => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        (T j) (f j)
      (∀ j ∈ J, P.time j n ∈ (M j).domain) ∧
        (∑ j ∈ J, ‖(M j).state (P.time j n) -
          freeEnergyState hDensity hSob (P.time j n) (P.profile j)‖) < ε := by
  have hc := finite_profile_control hDensity hSob h0 hfree hret hefree heret hH hA J
  exact eventually_atTop.1 (hc.1.and (hc.2.eventually (gt_mem_nhds hε)))

end HartreeF.CountableNonlinearProfiles
