import FActualRecenterBadTransport

/-! A normalized, time-recentered global trajectory is the canonical actual
maximal solution through the normalized sampled datum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace HartreeF.Paper121NormalizedGlobal
open EnergySpace MaximalTrajectory CriticalAffine BilateralPathTools
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain

theorem normalized_global_trajectory
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (f : EnergyState) (c : ℝ) {a : ℝ} (ha : 0 < a) (y : Space) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f
    M.domain = univ →
    let z := (criticalAffineState a ha y).symm (M.state c)
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 z
    U.domain = univ ∧ ∀ t,
      U.state t = (criticalAffineState a ha y).symm (M.state (c+a^2*t)) := by
  intro M hglobal z U
  have hc : c ∈ M.domain := by rw [hglobal]; trivial
  let N := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH c (M.state c)
  have hNM := actualMaximalTrajectory_recenter hDensity hSob h0 hfree hret hefree heret hH f hc
  let covarianceAt : ℝ → EnergyState → Prop := fun mark datum =>
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH mark datum
    V.domain = (AffineMixed.timeAffine a c) ⁻¹' N.domain ∧
      EqOn V.state (fun s => affineState ha y (N.state (AffineMixed.timeAffine a c s))) V.domain
  have hraw : covarianceAt ((c-c)/a^2) (affineState ha y (M.state c)) :=
    MaximalAffine.actualMaximalTrajectory_affine hDensity hSob h0 hfree hret hefree heret hH
      ha y c c (M.state c)
  have hmark : (c-c)/a^2 = 0 := by simp only [sub_self, zero_div]
  have hdatum : affineState ha y (M.state c) = z :=
    (criticalAffineState_symm_eq_affineState _ _ _ _).symm
  have hcov : covarianceAt 0 z := Eq.mp (congrArg₂ covarianceAt hmark hdatum) hraw
  have hN : N.domain = univ := hNM.1.trans hglobal
  have hU : U.domain = univ := hcov.1.trans (by rw [hN, preimage_univ])
  refine ⟨hU, ?_⟩
  intro t
  have ht : t ∈ U.domain := by rw [hU]; trivial
  have htM : AffineMixed.timeAffine a c t ∈ M.domain := by rw [hglobal]; trivial
  rw [hcov.2 ht, hNM.2 htM, criticalAffineState_symm_eq_affineState]
  congr 2
  exact add_comm _ _

end HartreeF.Paper121NormalizedGlobal
