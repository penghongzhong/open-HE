import FActualFiniteSCurveFinite
import FActualMaximalAffineCovariance
import FCriticalAffineIsometry
import FR2ActualProfileFrames
import FR2CompactSmallData

/-! Zero-mark global finite X transports to the original marked canonical
curve. A genuine recentering uses the existing full state-equality theorem.
No new PDE, replacement nonlinear profile, or finite-X producer is assumed.
Static author source; UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteSActualX
open EnergySpace CriticalPathSpace MaximalTrajectory SobolevStretch StationarySelfTest
  Retarded ActualStrichartz EndpointOutput ForcingDomain R2Global R2Frames
  CriticalAffine AffineMixed
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath

private theorem criticalAffineState_one_zero (u : EnergyState) :
    criticalAffineState 1 (by norm_num) 0 u = u := by
  change affineState (inv_pos.mpr (by norm_num : (0 : ℝ) < 1))
    (-((1 : ℝ)⁻¹ • (0 : Space))) u = u
  simp only [inv_one, smul_zero, neg_zero, affineState_one_zero]

/-- Scale one, spatial center zero and original affine shift s give
V(t)=U(t+s); the inverse state frame has time parameter -s. -/
theorem actualMaximalTrajectory_marked_global_curveFinite
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c)
    (s : ℝ) (f : EnergyState)
    (hzero :
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain = Set.univ ∧
      CurveFinite (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).state) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
    U.domain = Set.univ ∧ CurveFinite U.state := by
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f
  have hone : (0 : ℝ) < 1 := by norm_num
  have hcov : V.domain = (fun t : ℝ => t+s) ⁻¹' U.domain ∧
      Set.EqOn V.state (fun t => U.state (t+s)) V.domain := by
    have hc := MaximalAffine.actualMaximalTrajectory_affine
      hDensity hSob h0 hfree hret hefree heret hH hone (0 : Space) s s f
    dsimp only at hc
    rw [sub_self, zero_div, affineState_one_zero] at hc
    simpa only [affineState_one_zero, timeAffine, one_pow, one_mul] using hc
  have hglobal : U.domain = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro t
    have ht : t-s ∈ V.domain := hzero.1.symm ▸ Set.mem_univ (t-s)
    have hu : t-s ∈ (fun t : ℝ => t+s) ⁻¹' U.domain := hcov.1 ▸ ht
    simpa only [Set.mem_preimage, sub_add_cancel] using hu
  have hframe : stateFrame V.state hone (0 : Space) (-s) = U.state := by
    funext t
    rw [stateFrame_time, criticalAffineState_one_zero]
    have ht : -s + t / (1 : ℝ)^2 = t-s := by ring
    rw [ht]
    have hv := hcov.2 (x := t-s) (hzero.1.symm ▸ Set.mem_univ (t-s))
    simpa only [sub_add_cancel] using hv
  refine ⟨hglobal, ?_⟩
  rw [← hframe]
  exact R2Frames.CurveFinite.stateFrame hzero.2 hone (0 : Space) (-s)

/-- A finite-X canonical solution at a genuine matching state globalizes
and identifies the original marked solution, using both maximal inclusions. -/
theorem actualMaximalTrajectory_global_curveFinite_of_recenter
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c T s : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c)
    (f : EnergyState)
    (hs : s ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f).domain)
    (hrec :
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f).state s)).domain = Set.univ ∧
      CurveFinite (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f).state s)).state) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
    M.domain = Set.univ ∧ CurveFinite M.state := by
  obtain ⟨hglobal, hstate⟩ := R2SmallData.actualMaximalTrajectory_global_of_recenter
    hDensity hSob h0 hfree hret hefree heret hH f hs hrec.1
  refine ⟨hglobal, ?_⟩
  rw [hstate]
  exact hrec.2

end HartreeF.FiniteSActualX
