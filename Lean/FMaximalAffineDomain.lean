import FAffineLocalMildTrajectory

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.MaximalAffine
open EnergySpace CriticalPathSpace CriticalUniqueness ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open AffinePath AffineMixed CriticalAffine NonlinearAffine MaximalTrajectory
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  affineCriticalPath actualMaximalTrajectory LocalMildTrajectory.path IsMildHartreePath

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr alpha kernel : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hH : OrdinaryHLS alpha kernel)

include hDensity hSob h0 hfree hret hH in
/-- Exact covariance of the union of all genuine local solution domains.
The reverse inclusion transforms a competing trajectory back; no extension
or global-existence conclusion is assumed. -/
theorem maximalDomain_affine {a : ℝ} (ha : 0<a) (b : Space) (c t0 : ℝ) (f : EnergyState) :
    maximalDomain alpha kernel t0 (affineState ha b f)=
      (timeAffine a c) ⁻¹' maximalDomain alpha kernel (timeAffine a c t0) f := by
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨V,htV⟩ := Set.mem_iUnion.mp ht
    let W := affineLocalMildTrajectory hDensity hSob h0 hfree hret hH
      (inv_pos.mpr ha) (-(a⁻¹ • b)) (-c/a^2) (timeAffine a c t0) V
      (timeAffine_inverse_left ha c t0)
    have htW : timeAffine a c t ∈ W.domain := by
      change timeAffine a⁻¹ (-c/a^2) (timeAffine a c t)∈V.domain
      rw [timeAffine_inverse_left ha c t]
      exact htV
    have hM := subset_maximalDomain W htW
    change timeAffine a c t∈maximalDomain alpha kernel (timeAffine a c t0) f
    simpa only [affineState_left_inverse] using hM
  · intro t ht
    obtain ⟨U,htU⟩ := Set.mem_iUnion.mp ht
    let V := affineLocalMildTrajectory hDensity hSob h0 hfree hret hH ha b c t0 U rfl
    exact subset_maximalDomain V htU

include hDensity hSob h0 hfree hret hH in
/-- The canonical same-datum maximal curves agree on the exact transformed
domain. Their arbitrary outside-domain values play no role. -/
theorem maximalState_affine {a : ℝ} (ha : 0<a) (b : Space) (c t0 : ℝ) (f : EnergyState)
    {t : ℝ} (ht : t∈maximalDomain alpha kernel t0 (affineState ha b f)) :
    maximalState alpha kernel t0 (affineState ha b f) t=
      affineState ha b (maximalState alpha kernel (timeAffine a c t0) f (timeAffine a c t)) := by
  have htM : timeAffine a c t∈maximalDomain alpha kernel (timeAffine a c t0) f := by
    rw [maximalDomain_affine hDensity hSob h0 hfree hret hH ha b c t0 f] at ht
    exact ht
  obtain ⟨U,htU⟩ := Set.mem_iUnion.mp htM
  let V := affineLocalMildTrajectory hDensity hSob h0 hfree hret hH ha b c t0 U rfl
  exact (maximalState_agrees hDensity hSob h0 hfree hret hH V htU).trans
    (congrArg (affineState ha b)
      (maximalState_agrees hDensity hSob h0 hfree hret hH U htU).symm)

include hDensity hSob h0 hfree hret hH in
/-- Original marked time s0 becomes precisely (s0-c)/a^2. -/
theorem maximalDomain_affine_marked {a : ℝ} (ha : 0<a) (b : Space) (c s0 : ℝ)
    (f : EnergyState) :
    maximalDomain alpha kernel ((s0-c)/a^2) (affineState ha b f)=
      (timeAffine a c) ⁻¹' maximalDomain alpha kernel s0 f := by
  have htime : timeAffine a c ((s0-c)/a^2)=s0 :=
    (timeAffineHomeomorph ha c).apply_symm_apply s0
  have h := maximalDomain_affine hDensity hSob h0 hfree hret hH ha b c ((s0-c)/a^2) f
  rw [htime] at h
  exact h

include hDensity hSob h0 hfree hret hH in
theorem maximalState_affine_marked {a : ℝ} (ha : 0<a) (b : Space) (c s0 : ℝ)
    (f : EnergyState) {t : ℝ}
    (ht : t∈maximalDomain alpha kernel ((s0-c)/a^2) (affineState ha b f)) :
    maximalState alpha kernel ((s0-c)/a^2) (affineState ha b f) t=
      affineState ha b (maximalState alpha kernel s0 f (timeAffine a c t)) := by
  have htime : timeAffine a c ((s0-c)/a^2)=s0 :=
    (timeAffineHomeomorph ha c).apply_symm_apply s0
  have h := maximalState_affine hDensity hSob h0 hfree hret hH ha b c ((s0-c)/a^2) f ht
  rw [htime] at h
  exact h

end HartreeF.MaximalAffine
