import FActualMaximalAffineCovariance
import FPathRestrictionLpNorms
import FSmallSTailContinuation

/-! Actual compact path identities used by bilateral concentration.
All comparisons are on native domains.  UNCOMPILED source-level draft. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.BilateralPathTools
open EnergySpace CriticalPathSpace CriticalPathRestriction IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open CriticalSourceBounds CriticalJointSources ActualSTail ActualPathPartitions
open AffinePath AffineMixed CriticalAffine MaximalTrajectory MaximalAffine
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  affineCriticalPath LocalMildTrajectory.path

/-- The constant is permitted to vanish; no division by it is used. -/
def graphSConstant (K : ℝ) : ℝ := 10 * K ^ (1/6 : ℝ)

theorem graphSConstant_nonneg {K : ℝ} (hSob : OrdinarySobolev K) :
    0 ≤ graphSConstant K :=
  mul_nonneg (by norm_num) (Real.rpow_nonneg hSob.nonneg _)

theorem pathValueSize_le_graph (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (q : CriticalPath (intervalMeasure a b)) :
    pathValueSize (intervalMeasure a b) q ≤ ENNReal.ofReal (graphSConstant K * ‖q‖) := by
  have hC : 0 ≤ (5/3 : ℝ) * K ^ (1/6 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hSob.nonneg _)
  calc
    _ ≤ ENNReal.ofReal ((5/3 : ℝ)*K^(1/6 : ℝ)) *
        (6 * ENNReal.ofReal ‖q‖) :=
      (joint_value_critical_bound _ hDensity hSob q).trans
        (mul_le_mul' le_rfl (joint_gradient_bound _ q))
    _ = ENNReal.ofReal (((5/3 : ℝ)*K^(1/6 : ℝ)) * (6*‖q‖)) := by
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]
      norm_num
    _ = _ := by congr 1; unfold graphSConstant; ring

/-- Canonical choices of a compact path agree when their actual states agree. -/
theorem path_eq_of_state_eqOn {alpha kernel s t a b : ℝ} {f g : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (V : LocalMildTrajectory alpha kernel t g)
    (hab : a ≤ b) (hU : Icc a b ⊆ U.domain) (hV : Icc a b ⊆ V.domain)
    (heq : Set.EqOn U.state V.state (Icc a b)) : U.path hab hU = V.path hab hV := by
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro x
  exact (U.path_agrees hab hU x).trans
    ((heq x.property).trans (V.path_agrees hab hV x).symm)

/-- A restriction is the actual path of the same trajectory on the subinterval. -/
theorem path_restrict {alpha kernel s a b c d : ℝ} {f : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (hab : a ≤ b)
    (hU : Icc a b ⊆ U.domain) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (hV : Icc c d ⊆ U.domain) :
    U.path hcd hV = restrictPath hac hcd hdb (U.path hab hU) := by
  apply energyPath_injective (intervalMeasure c d)
  apply ContinuousMap.ext
  intro x
  rw [restrictPath_energy, U.path_agrees, U.path_agrees]
  rfl

/-- Re-marking preserves exactly the native maximal domain and its states.
There is deliberately no equality of the arbitrary outside-domain fills. -/
theorem actualMaximalTrajectory_recenter (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s c : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (f : EnergyState)
    (hc : c ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f).domain) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
    let N := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH c (M.state c)
    N.domain = M.domain ∧ Set.EqOn N.state M.state M.domain := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  let R := M.recenter c hc
  let N := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH c (M.state c)
  have hMN : M.domain ⊆ N.domain := subset_maximalDomain R
  have hsN : s ∈ N.domain := hMN M.center_mem
  have hs : N.state s = f :=
    (LocalMildTrajectory.overlap_eq hDensity hSob h0 hfree hret hH N R hsN M.center_mem).trans
      M.initial
  let W := N.recenterWithDatum s f hsN hs
  have hNM : N.domain ⊆ M.domain := subset_maximalDomain W
  refine ⟨Set.Subset.antisymm hNM hMN, ?_⟩
  intro t ht
  exact LocalMildTrajectory.overlap_eq hDensity hSob h0 hfree hret hH N R (hMN ht) ht

/-- Native zero-mark recentering, including the exact shifted lifespan. -/
theorem actualMaximalTrajectory_zero_recenter (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s c : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (f : EnergyState)
    (hc : c ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f).domain) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (M.state c)
    U.domain = (fun t : ℝ => c+t) ⁻¹' M.domain ∧
      Set.EqOn U.state (fun t => M.state (c+t)) U.domain := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  let N := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH c (M.state c)
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (M.state c)
  have hNM := actualMaximalTrajectory_recenter hDensity hSob h0 hfree hret hefree heret hH f hc
  have hUN : U.domain = (fun t : ℝ => c+t) ⁻¹' N.domain ∧
      Set.EqOn U.state (fun t => N.state (c+t)) U.domain := by
    have hone : (0 : ℝ) < 1 := by norm_num
    let covarianceAt : ℝ → EnergyState → Prop := fun mark datum =>
      let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH mark datum
      V.domain = (timeAffine 1 c) ⁻¹' N.domain ∧
        Set.EqOn V.state (fun t => affineState hone 0 (N.state (timeAffine 1 c t))) V.domain
    have hraw : covarianceAt ((c - c) / (1 : ℝ) ^ 2)
        (affineState hone 0 (M.state c)) :=
      actualMaximalTrajectory_affine hDensity hSob h0 hfree hret hefree heret hH
        hone (0 : Space) c c (M.state c)
    have hmark : (c - c) / (1 : ℝ) ^ 2 = 0 := by
      simp only [sub_self, zero_div]
    have hdatum : affineState hone 0 (M.state c) = M.state c :=
      affineState_one_zero (M.state c)
    have htransport : covarianceAt ((c - c) / (1 : ℝ) ^ 2)
        (affineState hone 0 (M.state c)) = covarianceAt 0 (M.state c) :=
      congrArg₂ covarianceAt hmark hdatum
    have hnormalized : covarianceAt 0 (M.state c) := Eq.mp htransport hraw
    have htime : timeAffine 1 c = (fun t : ℝ => c + t) := by
      funext t
      simp only [timeAffine, one_pow, one_mul]
      exact add_comm t c
    refine ⟨hnormalized.1.trans
      (congrArg (fun f : ℝ → ℝ => f ⁻¹' N.domain) htime), ?_⟩
    intro t ht
    exact ((hnormalized.2 ht).trans (affineState_one_zero _)).trans
      (congrArg N.state (congrFun htime t))
  have hdom : U.domain = (fun t : ℝ => c+t) ⁻¹' M.domain :=
    hUN.1.trans (congrArg (fun D : Set ℝ => (fun t : ℝ => c+t) ⁻¹' D) hNM.1)
  refine ⟨hdom, ?_⟩
  intro t ht
  have htPre : t ∈ (fun x : ℝ => c + x) ⁻¹' M.domain := hdom ▸ ht
  have htM : c + t ∈ M.domain := htPre
  exact (hUN.2 ht).trans (hNM.2 htM)

/-- Compact path identity for any actual affine state agreement. -/
theorem affine_path_of_state_eqOn {alpha kernel s t : ℝ} {f g : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f) (V : LocalMildTrajectory alpha kernel t g)
    {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
    (hU : Icc (timeAffine a c A) (timeAffine a c B) ⊆ U.domain)
    (hV : Icc A B ⊆ V.domain)
    (heq : Set.EqOn V.state (fun x => affineState ha b (U.state (timeAffine a c x)))
      (Icc A B)) :
    V.path hAB hV = affineCriticalPath ha b c A B hAB
      (U.path (timeAffine_monotone ha c hAB) hU) := by
  apply energyPath_injective (intervalMeasure A B)
  apply ContinuousMap.ext
  intro x
  rw [V.path_agrees, affineCriticalPath_energy_apply, U.path_agrees]
  exact heq x.property

/-- Actual canonical affine compact identity with both true domains explicit. -/
theorem actualMaximalTrajectory_affine_path (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    {a : ℝ} (ha : 0<a) (b : Space) (c s : ℝ) (f : EnergyState) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
      ((s-c)/a^2) (affineState ha b f)
    ∀ (A B : ℝ) (hAB : A≤B)
      (hU : Icc (timeAffine a c A) (timeAffine a c B) ⊆ U.domain)
      (hV : Icc A B ⊆ V.domain),
      V.path hAB hV = affineCriticalPath ha b c A B hAB
        (U.path (timeAffine_monotone ha c hAB) hU) := by
  intro U V A B hAB hU hV
  exact affine_path_of_state_eqOn U V ha b c A B hAB hU hV
    (fun _ hx => (actualMaximalTrajectory_affine
      hDensity hSob h0 hfree hret hefree heret hH ha b c s f).2 (hV hx))

/-- Exact graph isometry; this is spatial/time covariance, not a free-frame claim. -/
theorem actualMaximalTrajectory_affine_norm (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    {a : ℝ} (ha : 0<a) (b : Space) (c s : ℝ) (f : EnergyState) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
      ((s-c)/a^2) (affineState ha b f)
    ∀ (A B : ℝ) (hAB : A≤B)
      (hU : Icc (timeAffine a c A) (timeAffine a c B) ⊆ U.domain)
      (hV : Icc A B ⊆ V.domain),
      ‖V.path hAB hV‖ = ‖U.path (timeAffine_monotone ha c hAB) hU‖ := by
  intro U V A B hAB hU hV
  rw [actualMaximalTrajectory_affine_path hDensity hSob h0 hfree hret hefree heret hH
    ha b c s f A B hAB hU hV]
  exact affineCriticalPath_norm ha b c A B hAB _

end HartreeF.BilateralPathTools
