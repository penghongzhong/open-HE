import FIndependentNonlinearAffineTrajectory

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
namespace HartreeF.MaximalAffine
open EnergySpace CriticalPathSpace CriticalUniqueness ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open AffinePath AffineMixed CriticalAffine NonlinearAffine MaximalTrajectory
open NonlinearAffineTrajectoryReview
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  affineCriticalPath actualMaximalTrajectory LocalMildTrajectory.path IsMildHartreePath

/-- The inverse positive parabolic time frame, with the original time origin
kept explicit. -/
theorem timeAffine_inverse_left {a : ℝ} (ha : 0<a) (c t : ℝ) :
    timeAffine a⁻¹ (-c/a^2) (timeAffine a c t)=t := by
  unfold timeAffine
  field_simp
  ring

theorem timeAffine_inverse_right {a : ℝ} (ha : 0<a) (c t : ℝ) :
    timeAffine a c (timeAffine a⁻¹ (-c/a^2) t)=t := by
  unfold timeAffine
  field_simp
  ring

/-- Pull back an actual local mild trajectory, including its whole open time
domain and every compact mild segment. All fields are produced. -/
def affineLocalMildTrajectory (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel s0 : ℝ} {f : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha kernel) {a : ℝ} (ha : 0<a) (b : Space) (c t0 : ℝ)
    (U : LocalMildTrajectory alpha kernel s0 f) (hcenter : timeAffine a c t0=s0) :
    LocalMildTrajectory alpha kernel t0 (affineState ha b f) where
  domain := (timeAffine a c) ⁻¹' U.domain
  state := fun t => affineState ha b (U.state (timeAffine a c t))
  domain_open := U.domain_open.preimage (timeAffineHomeomorph ha c).continuous
  domain_connected := by
    constructor
    intro x hx y hy t ht
    exact U.domain_connected.out' hx hy
      ⟨timeAffine_monotone ha c ht.1,timeAffine_monotone ha c ht.2⟩
  center_mem := by change timeAffine a c t0∈U.domain; rw [hcenter]; exact U.center_mem
  continuous := (affineStateEquiv ha b).continuous.continuousOn.comp
    (U.continuous.comp (timeAffineHomeomorph ha c).continuous.continuousOn
      (fun _ ht => ht)) (fun _ _ => Set.mem_univ _)
  initial := by rw [hcenter,U.initial]
  compact := by
    intro A B hAB hI
    have hmap : Icc (timeAffine a c A) (timeAffine a c B) ⊆ U.domain := by
      intro s hs
      let t := (timeAffineHomeomorph ha c).symm s
      have htime : timeAffine a c t=s := (timeAffineHomeomorph ha c).apply_symm_apply s
      have ht : t∈Icc A B := by
        rw [← timeAffine_preimage_Icc ha c A B]
        change timeAffine a c t ∈ Icc (timeAffine a c A) (timeAffine a c B)
        rw [htime]
        exact hs
      have hm := hI ht
      change timeAffine a c t∈U.domain at hm
      rwa [htime] at hm
    obtain ⟨v,hv,hm,_⟩ := local_mild_trajectory_affine_segment
      hDensity hSob h0 hfree hret hH U ha b c A B hAB hmap
    exact ⟨v,hv,hm⟩

@[simp] theorem affineLocalMildTrajectory_domain (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel s0 : ℝ} {f : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha kernel) {a : ℝ} (ha : 0<a) (b : Space) (c t0 : ℝ)
    (U : LocalMildTrajectory alpha kernel s0 f) (hcenter : timeAffine a c t0=s0) :
    (affineLocalMildTrajectory hDensity hSob h0 hfree hret hH ha b c t0 U hcenter).domain=
      (timeAffine a c) ⁻¹' U.domain := rfl

@[simp] theorem affineLocalMildTrajectory_state (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel s0 : ℝ} {f : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha kernel) {a : ℝ} (ha : 0<a) (b : Space) (c t0 : ℝ)
    (U : LocalMildTrajectory alpha kernel s0 f) (hcenter : timeAffine a c t0=s0) (t : ℝ) :
    (affineLocalMildTrajectory hDensity hSob h0 hfree hret hH ha b c t0 U hcenter).state t=
      affineState ha b (U.state (timeAffine a c t)) := rfl

end HartreeF.MaximalAffine
