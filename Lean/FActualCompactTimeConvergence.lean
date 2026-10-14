import FActualFiniteSideGraphStability
import FR2CompactSmallData

/-! Compact-time continuous dependence and moving-time convergence for the
actual maximal Hartree trajectories. All path bounds and zero forcing are
derived from the reference local mild trajectory. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualCompactTimeConvergence
open EnergySpace CriticalPathSpace ActualDuhamelPath MaximalTrajectory
open CriticalSourceBounds SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness EndpointOutput HartreeDistributionalBridge
open LinearWeakEquation L1RetardedIndependentReview
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalGradient hartreeDuhamelMap criticalPathIntervalSource LocalMildTrajectory.path
  actualMaximalTrajectory CriticalJointSources.jointFields

private theorem state_difference_le_path
    {alpha kernel s r a b : ℝ} {f g : EnergyState}
    (U : LocalMildTrajectory alpha kernel s f)
    (V : LocalMildTrajectory alpha kernel r g) (hab : a ≤ b)
    (hU : Icc a b ⊆ U.domain) (hV : Icc a b ⊆ V.domain)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖U.state t - V.state t‖ ≤ ‖U.path hab hU - V.path hab hV‖ := by
  have hsub := congrArg (fun q : C(Icc a b, EnergyState) => q ⟨t, ht⟩)
    ((energyPath (intervalMeasure a b)).map_sub (U.path hab hU) (V.path hab hV))
  have he : energyPath (intervalMeasure a b) (U.path hab hU - V.path hab hV) ⟨t, ht⟩ =
      U.state t - V.state t :=
    hsub.trans (congrArg₂ (fun x y : EnergyState => x - y)
      (U.path_agrees hab hU ⟨t, ht⟩) (V.path_agrees hab hV ⟨t, ht⟩))
  exact (congrArg norm he).symm.trans_le
    (R2SmallData.represented_state_norm_le _ ⟨t, ht⟩)

/-- Actual interval inclusion and uniform state error, with no assumed
bound on the perturbed trajectory. -/
theorem exists_forward_compact_state_bound
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    {a b : ℝ} (hab : a ≤ b) (psi : EnergyState)
    (V : LocalMildTrajectory alpha kernel a psi) (hI : Icc a b ⊆ V.domain) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ f : EnergyState, ‖f - psi‖ ≤ δ →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a f
      Icc a b ⊆ U.domain ∧
        ∀ t ∈ Icc a b, ‖U.state t - V.state t‖ ≤ C * ‖f - psi‖ := by
  let q := V.path hab hI
  have hfinite : pathValueSize (intervalMeasure a b) q ≠ ⊤ :=
    (CriticalJointSources.joint_value_critical (intervalMeasure a b) hDensity hSob q).2
  have hsize : pathValueSize (intervalMeasure a b) q ≤
      ENNReal.ofReal (pathValueSize (intervalMeasure a b) q).toReal :=
    (ENNReal.ofReal_toReal hfinite).symm.le
  have hpde : ForcedHartreeCompactTestIdentity alpha kernel hab q (zeroSource a b) :=
    HartreeMildPDEProducer.actual_zero_compactPDE_of_original_mild
      hDensity hSob hH h0 hfree hret hab q (V.state a) hgen (V.path_mild hab hI)
  obtain ⟨δ, C, hδ, _hδ1, hC, hperturb⟩ :=
    CompactLongTimePerturbation.exists_actual_maximal_compact_perturbation
      (B := ‖energyPath (intervalMeasure a b) q‖)
      (M := (pathValueSize (intervalMeasure a b) q).toReal)
      hDensity hSob h0 hfree hret hefree heret hH hgen hUnique
      (norm_nonneg (energyPath (intervalMeasure a b) q)) ENNReal.toReal_nonneg
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro f hf
  have hinit : ‖f - energyPath _ q ⟨a, le_rfl, hab⟩‖ ≤ ‖f - psi‖ := by
    simp only [q, V.path_agrees, V.initial, le_refl]
  have herr : ‖(zeroSource a b).gradient‖ ≤ ‖f - psi‖ := by
    simpa only [zeroSource, norm_zero] using norm_nonneg (f - psi)
  obtain ⟨hU, hresult⟩ := hperturb hab f q (zeroSource a b) hpde le_rfl hsize
    (norm_nonneg _) hf hinit herr
  refine ⟨hU, ?_⟩
  intro t ht
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH a f
  have hclose : ‖U.path hab hU - q‖ ≤ C * ‖f - psi‖ := hresult.2.2.2.2.1
  exact (state_difference_le_path U V hab hU hI t ht).trans hclose

/-- Actual interval inclusion and uniform state error, with no assumed
bound on the perturbed trajectory. -/
theorem exists_backward_compact_state_bound
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    {a b : ℝ} (hab : a ≤ b) (psi : EnergyState)
    (V : LocalMildTrajectory alpha kernel b psi) (hI : Icc a b ⊆ V.domain) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ f : EnergyState, ‖f - psi‖ ≤ δ →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH b f
      Icc a b ⊆ U.domain ∧
        ∀ t ∈ Icc a b, ‖U.state t - V.state t‖ ≤ C * ‖f - psi‖ := by
  let q := V.path hab hI
  have hfinite : pathValueSize (intervalMeasure a b) q ≠ ⊤ :=
    (CriticalJointSources.joint_value_critical (intervalMeasure a b) hDensity hSob q).2
  have hsize : pathValueSize (intervalMeasure a b) q ≤
      ENNReal.ofReal (pathValueSize (intervalMeasure a b) q).toReal :=
    (ENNReal.ofReal_toReal hfinite).symm.le
  have hpde : ForcedHartreeCompactTestIdentity alpha kernel hab q (zeroSource a b) :=
    HartreeMildPDEProducer.actual_zero_compactPDE_of_original_mild
      hDensity hSob hH h0 hfree hret hab q (V.state a) hgen (V.path_mild hab hI)
  obtain ⟨δ, C, hδ, _hδ1, hC, hperturb⟩ :=
    BackwardCompactLongTimePerturbation.exists_actual_maximal_backward_compact_perturbation
      (B := ‖energyPath (intervalMeasure a b) q‖)
      (M := (pathValueSize (intervalMeasure a b) q).toReal)
      hDensity hSob h0 hfree hret hefree heret hH hgen hUnique
      (norm_nonneg (energyPath (intervalMeasure a b) q)) ENNReal.toReal_nonneg
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro f hf
  have hinit : ‖f - energyPath _ q ⟨b, hab, le_rfl⟩‖ ≤ ‖f - psi‖ := by
    simp only [q, V.path_agrees, V.initial, le_refl]
  have herr : ‖(zeroSource a b).gradient‖ ≤ ‖f - psi‖ := by
    simpa only [zeroSource, norm_zero] using norm_nonneg (f - psi)
  obtain ⟨hU, hresult⟩ := hperturb hab f q (zeroSource a b) hpde le_rfl hsize
    (norm_nonneg _) hf hinit herr
  refine ⟨hU, ?_⟩
  intro t ht
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH b f
  have hclose : ‖U.path hab hU - q‖ ≤ C * ‖f - psi‖ := hresult.2.2.2.2.1
  exact (state_difference_le_path U V hab hU hI t ht).trans hclose

/-- The moving evaluation statement needed in the critical-limit argument.
The reference solution need only exist on the displayed compact time window.
Both signs of the moving time are covered by the literal forward/backward
perturbation theorems, without time reversal. -/
theorem actual_moving_time_tendsto
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (psi : EnergyState) (z : ℕ → EnergyState)
    (hz : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0))
    {a b t : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (tau : ℕ → ℝ) (htau : Tendsto tau atTop (𝓝 t))
    (ht : t ∈ Icc a b) (htauI : ∀ᶠ n in atTop, tau n ∈ Icc a b) :
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi
    Icc a b ⊆ V.domain →
      (∀ᶠ n in atTop, Icc a b ⊆
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n)).domain) ∧
      Tendsto (fun n =>
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n)).state
          (tau n)) atTop (𝓝 (V.state t)) := by
  intro V hI
  have hIf : Icc 0 b ⊆ V.domain := fun _ hs => hI ⟨ha.trans hs.1, hs.2⟩
  have hIb : Icc a 0 ⊆ V.domain := fun _ hs => hI ⟨hs.1, hs.2.trans hb⟩
  obtain ⟨δf, Cf, hδf, hCf, hf⟩ := exists_forward_compact_state_bound
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hb psi V hIf
  obtain ⟨δb, Cb, hδb, hCb, hbnd⟩ := exists_backward_compact_state_bound
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique ha psi V hIb
  have hevent : ∀ᶠ n in atTop,
      Icc a b ⊆ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        0 (z n)).domain ∧
      ∀ s ∈ Icc a b,
        ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
          0 (z n)).state s - V.state s‖ ≤ (Cf + Cb) * ‖z n - psi‖ := by
    filter_upwards [hz.eventually_lt_const hδf, hz.eventually_lt_const hδb] with n hnf hnb
    obtain ⟨hUf, hsf⟩ := hf (z n) hnf.le
    obtain ⟨hUb, hsb⟩ := hbnd (z n) hnb.le
    constructor
    · intro s hs
      by_cases hsign : 0 ≤ s
      · exact hUf ⟨hsign, hs.2⟩
      · exact hUb ⟨hs.1, (lt_of_not_ge hsign).le⟩
    · intro s hs
      by_cases hsign : 0 ≤ s
      · exact (hsf s ⟨hsign, hs.2⟩).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
      · exact (hsb s ⟨hs.1, (lt_of_not_ge hsign).le⟩).trans
          (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  refine ⟨hevent.mono (fun _ hn => hn.1), ?_⟩
  have href : Tendsto (fun n => V.state (tau n)) atTop (𝓝 (V.state t)) :=
    ((V.continuous.mono hI) t ht).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨htau, htauI⟩)
  have herror : Tendsto (fun n =>
      ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        0 (z n)).state (tau n) - V.state (tau n)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [mul_zero] using hz.const_mul (Cf + Cb))
    filter_upwards [hevent, htauI] with n hn htn
    exact hn.2 (tau n) htn
  apply href.congr_dist
  simpa only [dist_eq_norm, norm_sub_rev] using herror

end HartreeF.ActualCompactTimeConvergence

