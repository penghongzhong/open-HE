import FNonlinearAffineRetarded
import FAffineCriticalPathLinearity
import FMildHartreeDefinition
import FActualAffineRetardedCovariance

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Set
namespace HartreeF.NonlinearAffine
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest ForcingDomain
open TimeHolder Retarded ActualStrichartz ActualDuhamelPath IntervalTimeTransport
open AffinePath AffineMixed AffineL1Source CriticalAffine CriticalUniqueness RawStabilityInputs
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath energyDistribution
  criticalPathIntervalSource affineCriticalPath intervalRetardedCriticalPath
  hartreeDuhamelMap freeCriticalPath freeEnergyState parabolicCompactSource
  RawSpatialGradientSource.compactSource CompatibleL1IntervalSource.retardedCriticalPath

variable (hDensity : OrdinaryH1Density) {K C0 Ch Cr alpha kernel : ℝ}
  (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
  (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hH : OrdinaryHLS alpha kernel) {a : ℝ} (ha : 0<a) (b : Space) (c A B : ℝ) (hAB : A≤B)
  (u0 : EnergyState)
  (u : CriticalPath (intervalMeasure (timeAffine a c A) (timeAffine a c B)))

/-- The actual Hartree Duhamel map commutes with the constructed path action.
Both nonlinear source classes and their weak gradients were identified natively. -/
theorem hartreeDuhamelMap_affine :
    hartreeDuhamelMap hDensity hSob h0 hfree hret hH hAB (affineState ha b u0)
      (affineCriticalPath ha b c A B hAB u)=
    affineCriticalPath ha b c A B hAB
      (hartreeDuhamelMap hDensity hSob h0 hfree hret hH (timeAffine_monotone ha c hAB) u0 u) := by
  unfold hartreeDuhamelMap
  rw [affineCriticalPath_add,affineCriticalPath_smul]
  exact congrArg₂ (fun x y : CriticalPath (intervalMeasure A B) => x+Complex.I • y)
    (shifted_free_affine_covariance ha b c A B hAB hDensity hSob hfree u0)
    (nonlinear_retarded_affine_covariance hDensity hSob h0 hret hH ha b c A B hAB u)

include hDensity hSob h0 hfree hret hH in
/-- Literal nonlinear mild covariance on the original homogeneous state space.
No original scalar-L2 condition or additional W premise is introduced. -/
theorem isMildHartreePath_affine
    (hu : IsMildHartreePath (timeAffine_monotone ha c hAB) alpha kernel u0 u) :
    IsMildHartreePath hAB alpha kernel (affineState ha b u0)
      (affineCriticalPath ha b c A B hAB u) := by
  apply (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hAB
    (affineState ha b u0) (affineCriticalPath ha b c A B hAB u)).2
  have hfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
    (timeAffine_monotone ha c hAB) u0 u).1 hu
  exact (hartreeDuhamelMap_affine hDensity hSob h0 hfree hret hH ha b c A B hAB u0 u).trans
    (congrArg (affineCriticalPath ha b c A B hAB) hfix)

include hDensity hSob h0 hfree hret hH in
/-- The same actual transformed mild path, its derived initial trace and exact
continuous-energy/critical-gradient graph norm. Singleton intervals are retained. -/
theorem affine_actual_mild_path
    (hu : IsMildHartreePath (timeAffine_monotone ha c hAB) alpha kernel u0 u) :
    let v := affineCriticalPath ha b c A B hAB u
    IsMildHartreePath hAB alpha kernel (affineState ha b u0) v ∧
    energyPath _ v ⟨A,le_rfl,hAB⟩=affineState ha b u0 ∧ ‖v‖=‖u‖ := by
  dsimp only
  have hv := isMildHartreePath_affine hDensity hSob h0 hfree hret hH ha b c A B hAB u0 u hu
  refine ⟨hv,?_,affineCriticalPath_norm ha b c A B hAB u⟩
  have hfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hAB
    (affineState ha b u0) (affineCriticalPath ha b c A B hAB u)).1 hv
  exact (congrArg (fun w => energyPath (intervalMeasure A B) w ⟨A,le_rfl,hAB⟩) hfix).symm.trans
    (hartreeDuhamelMap_initial hDensity hSob h0 hfree hret hH hAB
      (affineState ha b u0) (affineCriticalPath ha b c A B hAB u))

/-- Actual forced nonlinear covariance keeps the same supplied perturbation
error at local scalar L1 and genuine vector N. Its transformed source is produced. -/
theorem affine_forced_hartree_path
    {I : Set ℝ} {e : ℝ → Space → ℂ} {G : ℝ → Space → SourceGradient}
    (hRaw : RawSpatialGradientSource I e G)
    (hI : Icc (timeAffine a c A) (timeAffine a c B) ⊆ I)
    (hu : u=hartreeDuhamelMap hDensity hSob h0 hfree hret hH
      (timeAffine_monotone ha c hAB) u0 u - Complex.I •
        (hRaw.compactSource (timeAffine_monotone ha c hAB) hI).retardedCriticalPath
          hDensity hSob h0 hret) :
    let v := affineCriticalPath ha b c A B hAB u
    v=hartreeDuhamelMap hDensity hSob h0 hfree hret hH hAB (affineState ha b u0) v - Complex.I •
      (parabolicCompactSource hRaw ha b c A B hAB hI).retardedCriticalPath hDensity hSob h0 hret := by
  dsimp only
  have ht := congrArg (affineCriticalPath ha b c A B hAB) hu
  rw [affineCriticalPath_sub,affineCriticalPath_smul] at ht
  exact ht.trans (congrArg₂ (fun x y : CriticalPath (intervalMeasure A B) => x-Complex.I • y)
    (hartreeDuhamelMap_affine hDensity hSob h0 hfree hret hH ha b c A B hAB u0 u).symm
    (raw_retarded_affine_covariance hDensity hSob h0 hret hRaw ha b c A B hAB hI).symm)

#print axioms hartreeDuhamelMap_affine
#print axioms isMildHartreePath_affine
#print axioms affine_actual_mild_path
#print axioms affine_forced_hartree_path
end HartreeF.NonlinearAffine
