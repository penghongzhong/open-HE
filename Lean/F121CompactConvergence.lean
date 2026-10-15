import FActualCompactTimeConvergence

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.Paper121CompactConvergence
open HartreeF.ActualCompactTimeConvergence
open EnergySpace CriticalPathSpace ActualDuhamelPath MaximalTrajectory
open CriticalSourceBounds SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness EndpointOutput HartreeDistributionalBridge
open LinearWeakEquation L1RetardedIndependentReview
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  criticalGradient hartreeDuhamelMap criticalPathIntervalSource LocalMildTrajectory.path
  actualMaximalTrajectory CriticalJointSources.jointFields

theorem uniform_compact_convergence
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
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi
    Icc a b ⊆ V.domain →
      (∀ᶠ n in atTop, Icc a b ⊆
        (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n)).domain) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Icc a b,
        ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
          0 (z n)).state t - V.state t‖ < ε := by
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
  intro ε hε
  have hlim : Tendsto (fun n => (Cf + Cb) * ‖z n - psi‖) atTop (𝓝 0) :=
    by simpa only [mul_zero] using hz.const_mul (Cf + Cb)
  filter_upwards [hevent, hlim.eventually_lt_const hε] with n hn hsmall
  intro t ht
  exact (hn.2 t ht).trans_lt hsmall

end HartreeF.Paper121CompactConvergence
