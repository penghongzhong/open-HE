import FActualHartreeCompactPDE
import FL1RetardedSubtraction
import FActualHartreeDuhamelDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.HartreeDistributionalBridge
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
open ActualDuhamelPath CriticalPathSpace IntervalTimeTransport ForcingDomain
open LinearWeakEquation L1RetardedIndependentReview FreeDataDependence
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule

theorem forced_response_algebra {M : Type*} [AddCommGroup M] [Module ℂ M]
    (x e n : M) : x - Complex.I • (e-n) = (x + Complex.I • n) - Complex.I • e := by
  rw [smul_sub]
  abel

variable (hDensity : OrdinaryH1Density) {K alpha c a b : ℝ}
  (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (hab : a ≤ b)
  (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b)

/-- Actual combined source e-N(q), carrying its actual spatial derivative. -/
def totalHartreeSource : CompatibleL1IntervalSource a b :=
  E.sub (actualHartreeSourceL1 hDensity hSob hH hab q)

theorem totalHartreeSource_gradient :
    (totalHartreeSource hDensity hSob hH hab q E).gradient = E.gradient -
      (criticalPathIntervalSource hDensity hSob hH hab q 0).gradient := rfl

/-- The combined source's actual representative is the literal e-N(q) function. -/
theorem totalHartreeSource_value_ae :
    ∀ᵐ s ∂localMeasure a b, (totalHartreeSource hDensity hSob hH hab q E).value s =ᵐ[volume]
      (fun x => E.value s x -
        forcing alpha c (energyValue (extendEnergyPath hab (energyPath _ q) s)) x) := by
  filter_upwards [E.sub_value_ae (actualHartreeSourceL1 hDensity hSob hH hab q),
    actualHartreeSourceL1_value_ae hDensity hSob hH hab q] with s hs hN
  change (E.sub (actualHartreeSourceL1 hDensity hSob hH hab q)).value s =ᵐ[volume] _
  rw [hs]
  filter_upwards [Lp.coeFn_sub (E.value s) ((actualHartreeSourceL1 hDensity hSob hH hab q).value s), hN]
    with x hx hNx
  simpa only [Pi.sub_apply, hNx] using hx

theorem totalHartreeSource_PDE
    (hPDE : ForcedHartreeCompactTestIdentity alpha c hab q E) :
    CompactTestIdentity a b
      (fun t => energyDistribution (extendEnergyPath hab (energyPath _ q) t))
      (fun t => Lp.toTemperedDistribution ((totalHartreeSource hDensity hSob hH hab q E).value t)) := by
  intro η hη φ hφ
  have he := actualHartree_subtracted_PDE hDensity hSob hH hab q E hPDE η hη φ hφ
  refine he.trans ?_
  symm
  apply integral_congr_ae
  filter_upwards [E.sub_distribution_ae (actualHartreeSourceL1 hDensity hSob hH hab q)] with t ht
  change η t * Lp.toTemperedDistribution
    ((E.sub (actualHartreeSourceL1 hDensity hSob hH hab q)).value t) φ = _
  rw [ht]

attribute [local irreducible] energyPath energyDistribution criticalGradient
  criticalPathIntervalSource intervalRetardedCriticalPath freeCriticalPath freeEnergyState
  hartreeDuhamelMap CompatibleL1IntervalSource.retardedCriticalPath actualRetardedCandidate

variable {C0 Ch Cr : ℝ} (h0 : OrdinaryEndpointBound C0)
  (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)

/-- Exact graph algebra identifies the generic total-source candidate with the
existing actual Hartree Duhamel map minus the genuine L1 error response. -/
theorem totalHartreeCandidate_energy (g : EnergyState) (t : Set.Icc a b) :
    actualRetardedCandidate hDensity hSob h0 hret hab
      (totalHartreeSource hDensity hSob hH hab q E) g t =
    energyPath _ (hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q -
      Complex.I • E.retardedCriticalPath hDensity hSob h0 hret) t := by
  have hR : (totalHartreeSource hDensity hSob hH hab q E).retardedCriticalPath hDensity hSob h0 hret =
      E.retardedCriticalPath hDensity hSob h0 hret -
        intervalRetardedCriticalPath hDensity hSob h0 hret
          (criticalPathIntervalSource hDensity hSob hH hab q 0) :=
    (E.retarded_sub (actualHartreeSourceL1 hDensity hSob hH hab q) hDensity hSob h0 hret).trans
      (congrArg (fun R : CriticalPath (intervalMeasure a b) =>
        E.retardedCriticalPath hDensity hSob h0 hret - R)
        (sourceL2ToL1_retarded_eq hDensity hSob h0 hret
          (criticalPathIntervalSource hDensity hSob hH hab q 0)))
  let RN := intervalRetardedCriticalPath hDensity hSob h0 hret
    (criticalPathIntervalSource hDensity hSob hH hab q 0)
  let RE := E.retardedCriticalPath hDensity hSob h0 hret
  let FF := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-a) g)
  let Φ := hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g q
  have htime : freeEnergyState hDensity hSob (t : ℝ) (freeEnergyState hDensity hSob (-a) g) =
      freeEnergyState hDensity hSob ((t : ℝ)-a) g :=
    (freeEnergyState_add_time hDensity hSob (t : ℝ) (-a) g).symm
  have hΦ : energyPath _ Φ t =
      freeEnergyState hDensity hSob ((t : ℝ)-a) g + Complex.I • energyPath _ RN t := by
    dsimp only [Φ]
    unfold hartreeDuhamelMap
    exact (criticalPath_energy_add_apply FF (Complex.I • RN) t).trans
      (congrArg₂ (fun x y : EnergyState => x+y)
        ((freeCriticalPath_energy hDensity hSob hfree a b
          (freeEnergyState hDensity hSob (-a) g) t).trans htime)
        (criticalPath_energy_smul_apply Complex.I RN t))
  have hRval : energyPath _
      ((totalHartreeSource hDensity hSob hH hab q E).retardedCriticalPath hDensity hSob h0 hret) t =
      energyPath _ RE t - energyPath _ RN t :=
    (congrArg (fun p : CriticalPath (intervalMeasure a b) => energyPath _ p t) hR).trans
      (criticalPath_energy_sub_apply RE RN t)
  have hleft : actualRetardedCandidate hDensity hSob h0 hret hab
      (totalHartreeSource hDensity hSob hH hab q E) g t =
      freeEnergyState hDensity hSob ((t : ℝ)-a) g -
        Complex.I • (energyPath _ RE t - energyPath _ RN t) := by
    unfold actualRetardedCandidate
    apply congrArg (fun w : EnergyState => freeEnergyState hDensity hSob ((t : ℝ)-a) g - Complex.I • w)
    exact (congrArg (fun s : Set.Icc a b => energyPath _
      ((totalHartreeSource hDensity hSob hH hab q E).retardedCriticalPath hDensity hSob h0 hret) s)
      (Set.projIcc_val hab t)).trans hRval
  have hright : energyPath _ (Φ - Complex.I • RE) t =
      (freeEnergyState hDensity hSob ((t : ℝ)-a) g + Complex.I • energyPath _ RN t) -
        Complex.I • energyPath _ RE t :=
    (criticalPath_energy_sub_apply Φ (Complex.I • RE) t).trans
      (congrArg₂ (fun x y : EnergyState => x-y) hΦ
        (criticalPath_energy_smul_apply Complex.I RE t))
  exact hleft.trans ((forced_response_algebra
    (freeEnergyState hDensity hSob ((t : ℝ)-a) g)
    (energyPath _ RE t) (energyPath _ RN t)).trans hright.symm)

/-- The actual forced mild identity is produced from the original distributional
Hartree PDE. It is a conclusion and not a premise. The scalar error remains L1. -/
theorem actual_forced_mild_of_distributional
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (hPDE : ForcedHartreeCompactTestIdentity alpha c hab q E) :
    q = hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab
      (energyPath _ q ⟨a, le_rfl, hab⟩) q -
      Complex.I • E.retardedCriticalPath hDensity hSob h0 hret := by
  let Q := extendEnergyPath hab (energyPath _ q)
  let F := totalHartreeSource hDensity hSob hH hab q E
  have hp : CompactWeakEquation a b (fun t => energyDistribution (Q t))
      (fun t => Lp.toTemperedDistribution (F.value t)) :=
    compactWeakEquation_of_actual_domains Q Q.continuous.continuousOn F.value F.value_integrable
      (totalHartreeSource_PDE hDensity hSob hH hab q E hPDE)
  apply energyPath_injective (intervalMeasure a b)
  apply ContinuousMap.ext
  intro t
  have he := compact_energy_eq_actual_candidate hDensity hSob h0 hret hab F hgen hUnique
    Q Q.continuous.continuousOn hp t
  have hQt : Q t = energyPath _ q t := extendEnergyPath_val hab (energyPath _ q) t
  have hQa : Q a = energyPath _ q ⟨a, le_rfl, hab⟩ := by
    change energyPath _ q (Set.projIcc a b hab a) = _
    exact congrArg (fun s : Set.Icc a b => energyPath _ q s) (Set.projIcc_left hab)
  exact hQt.symm.trans (he.trans ((congrArg (fun g : EnergyState =>
    actualRetardedCandidate hDensity hSob h0 hret hab F g t) hQa).trans
    (totalHartreeCandidate_energy hDensity hSob hH hab q E h0 hfree hret _ t)))

end HartreeF.HartreeDistributionalBridge
