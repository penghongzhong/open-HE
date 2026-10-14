import FActualResidualCompactSource
import FActualMildToForcedCompactPDE
import FIndependentNonlinearAffineTrajectory
import FR2ActualProfileFrames
import FR2FamilyTailAlgebra
import FEnergyFreeProperties

/-!
The finite sum of the actual framed nonlinear trajectories and the original
free remainder satisfies the compact forced Hartree equation with the SAME
subtraction-fold residual source. Static author source; UNCOMPILED.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap

namespace HartreeF.FullResidual
open EnergySpace Retarded SobolevStretch StationarySelfTest ActualStrichartz
  ActualDuhamelPath CriticalPathSpace IntervalTimeTransport ForcingDomain
  LinearWeakEquation L1RetardedIndependentReview HartreeDistributionalBridge
  HartreeMildPDEProducer CriticalUniqueness MaximalTrajectory CriticalAffine
  AffineMixed R2Global R2Frames R2FamilyTail ProfileEnergy NonlinearAffineTrajectoryReview
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  energyDistribution freeEnergyState extendEnergyPath

private theorem profileSum_integrable_range {a b : ℝ}
    (f : ℕ → ℝ → ℂ) (hf : ∀ j, IntegrableOn (f j) (Set.Icc a b)) (J : ℕ) :
    IntegrableOn (fun t => ∑ j ∈ Finset.range J, f j t) (Set.Icc a b) := by
  induction J with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty] using
      (integrable_zero ℝ ℂ (volume.restrict (Set.Icc a b)))
  | succ J ih =>
      simpa only [Finset.sum_range_succ] using ih.add (hf J)

private theorem profileSum_integral_range {a b : ℝ}
    (f : ℕ → ℝ → ℂ) (hf : ∀ j, IntegrableOn (f j) (Set.Icc a b)) (J : ℕ) :
    (∫ t in Set.Icc a b, ∑ j ∈ Finset.range J, f j t) =
      ∑ j ∈ Finset.range J, ∫ t in Set.Icc a b, f j t := by
  induction J with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, integral_zero]
  | succ J ih =>
      simp only [Finset.sum_range_succ]
      rw [integral_add (profileSum_integrable_range f hf J) (hf J), ih]

private theorem profileSum_weakOperator_add (p r : ℝ → EnergyState)
    (η : TimeTest) (φ : Test) (t : ℝ) :
    weakOperator (fun s => energyDistribution (p s + r s)) η φ t =
      weakOperator (fun s => energyDistribution (p s)) η φ t +
      weakOperator (fun s => energyDistribution (r s)) η φ t := by
  simp only [weakOperator, map_add, add_apply, mul_add]
  ring

private theorem profileSum_weakOperator_range (p : ℕ → ℝ → EnergyState)
    (J : ℕ) (η : TimeTest) (φ : Test) (t : ℝ) :
    weakOperator (fun s => energyDistribution (∑ j ∈ Finset.range J, p j s)) η φ t =
      ∑ j ∈ Finset.range J,
        weakOperator (fun s => energyDistribution (p j s)) η φ t := by
  induction J with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, weakOperator,
      map_zero, zero_apply, mul_zero, add_zero]
  | succ J ih =>
      simp only [Finset.sum_range_succ]
      rw [profileSum_weakOperator_add, ih]

private theorem profileSum_compactPath_extend {q : ℝ → EnergyState}
    (hq : CurveFinite q) {a b : ℝ} (hab : a ≤ b) (t : ℝ)
    (ht : t ∈ Set.Icc a b) :
    extendEnergyPath hab (energyPath _ (curveCompactPath hq hab)) t = q t :=
  (extendEnergyPath_val hab (energyPath _ (curveCompactPath hq hab)) ⟨t, ht⟩).trans
    (curveCompactPath_energy hq hab ⟨t, ht⟩)

private theorem profileSum_compactPath_weakIntegral {q : ℝ → EnergyState}
    (hq : CurveFinite q) {a b : ℝ} (hab : a ≤ b) (η : TimeTest) (φ : Test) :
    (∫ t in Set.Icc a b, weakOperator
      (fun s => energyDistribution
        (extendEnergyPath hab (energyPath _ (curveCompactPath hq hab)) s)) η φ t) =
    ∫ t in Set.Icc a b, weakOperator (fun s => energyDistribution (q s)) η φ t := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [weakOperator, profileSum_compactPath_extend hq hab t ht]

private theorem profileSum_zeroSource_pairIntegral {a b : ℝ}
    (η : TimeTest) (φ : Test) :
    (∫ t in Set.Icc a b,
      η t * Lp.toTemperedDistribution ((zeroSource a b).value t) φ) = 0 := by
  calc
    _ = ∫ _t in Set.Icc a b, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_zero (E := SourceSpace) (p := 1) (μ := localMeasure a b)] with t ht
      change η t * Lp.toTemperedDistribution
        ((0 : Lp SourceSpace 1 (localMeasure a b)) t) φ = 0
      rw [ht]
      have hz : Lp.toTemperedDistribution (0 : SourceSpace) = (0 : FreeFlow.TD) :=
        map_zero (Lp.toTemperedDistributionCLM ℂ (volume : Measure FreeFlow.V)
          (ENNReal.ofReal (6/5 : ℝ)))
      simp only [Pi.zero_apply, hz, zero_apply, mul_zero]
    _ = 0 := by simp only [integral_zero]

/-- The actual subtraction fold has the expected scalar test integral. Every
subtraction is justified by the genuine time-L1 source domains. -/
theorem sourceSubFold_pair_integral {a b : ℝ}
    (E : CompatibleL1IntervalSource a b) (S : ℕ → CompatibleL1IntervalSource a b)
    (J : ℕ) (η : TimeTest) (φ : Test) :
    (∫ t in Set.Icc a b,
      η t * Lp.toTemperedDistribution ((sourceSubFold E S J).value t) φ) =
    (∫ t in Set.Icc a b, η t * Lp.toTemperedDistribution (E.value t) φ) -
      ∑ j ∈ Finset.range J,
        ∫ t in Set.Icc a b, η t * Lp.toTemperedDistribution ((S j).value t) φ := by
  induction J with
  | zero => simp only [sourceSubFold, Finset.range_zero, Finset.sum_empty, sub_zero]
  | succ J ih =>
      have hfold := source_time_test_integrable (sourceSubFold E S J).value
        (sourceSubFold E S J).value_integrable η φ
      have hlast := source_time_test_integrable (S J).value (S J).value_integrable η φ
      have he :
          (∫ t in Set.Icc a b,
            η t * Lp.toTemperedDistribution ((sourceSubFold E S (J+1)).value t) φ) =
          ∫ t in Set.Icc a b, η t *
            (Lp.toTemperedDistribution ((sourceSubFold E S J).value t) -
              Lp.toTemperedDistribution ((S J).value t)) φ := by
        apply integral_congr_ae
        filter_upwards [(sourceSubFold E S J).sub_distribution_ae (S J)] with t ht
        change η t * Lp.toTemperedDistribution
          (((sourceSubFold E S J).sub (S J)).value t) φ = _
        rw [ht]
      rw [he, source_test_integral_sub _ _ η φ hfold hlast, ih,
        Finset.sum_range_succ]
      ring

/-- The original free remainder has its genuine linear zero-source weak
identity, based at the physical left endpoint. No nonlinear free-mild premise
is introduced. The all-Schwartz identity is used only for this linear term. -/
theorem originalFree_weakEquation (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hab : a ≤ b) (r : EnergyState) :
    WeakEquation a b
      (fun t => energyDistribution (freeEnergyState hDensity hSob t r)) (fun _ => 0) := by
  have h := actualFreeDistribution_weakEquation hgen hab
    (energyDistribution (freeEnergyState hDensity hSob a r))
  have he (t : ℝ) :
      FreeFlow.free (t-a) (energyDistribution (freeEnergyState hDensity hSob a r)) =
        energyDistribution (freeEnergyState hDensity hSob t r) := by
    calc
      _ = energyDistribution (freeEnergyState hDensity hSob (t-a)
          (freeEnergyState hDensity hSob a r)) :=
        (freeEnergyState_distribution hDensity hSob (t-a)
          (freeEnergyState hDensity hSob a r)).symm
      _ = _ := by rw [← freeEnergyState_add_time, sub_add_cancel]
  simpa only [he] using h

/-- Nonlinear covariance is taken from the actual affine mild-trajectory body.
Its compact path is identified with the SAME actual finite-X compact path by
energyPath injectivity, using the native inverse-scale affine parameters. -/
theorem framedTrajectory_compactPDE (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c s0 a b lambda : ℝ} {f : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (M : LocalMildTrajectory alpha c s0 f) (hglobal : M.domain = Set.univ)
    (hlambda : 0 < lambda) (y : Space) (tau : ℝ)
    (hp : CurveFinite (stateFrame M.state hlambda y tau)) (hab : a ≤ b) :
    ForcedHartreeCompactTestIdentity alpha c hab (curveCompactPath hp hab)
      (zeroSource a b) := by
  have hI : Set.Icc (timeAffine lambda⁻¹ tau a) (timeAffine lambda⁻¹ tau b) ⊆
      M.domain := by rw [hglobal]; exact Set.subset_univ _
  obtain ⟨v, hv, hmild, _htrace, _hnorm⟩ :=
    local_mild_trajectory_affine_segment hDensity hSob h0 hfree hret hH M
      (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) tau a b hab hI
  have he : v = curveCompactPath hp hab := by
    apply energyPath_injective (intervalMeasure a b)
    apply ContinuousMap.ext
    intro t
    calc
      energyPath _ v t = affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y))
          (M.state (timeAffine lambda⁻¹ tau t)) := hv t
      _ = stateFrame M.state hlambda y tau t := rfl
      _ = energyPath _ (curveCompactPath hp hab) t :=
        (curveCompactPath_energy hp hab t).symm
  rw [he] at hmild
  exact actual_zero_compactPDE_of_original_mild hDensity hSob hH h0 hfree hret hab
    (curveCompactPath hp hab)
    (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y))
      (M.state (timeAffine lambda⁻¹ tau a))) hgen hmild

private theorem profileSum_profileWeakIntegral (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    {p : ℝ → EnergyState} (hp : CurveFinite p) (hab : a ≤ b)
    (hPDE : ForcedHartreeCompactTestIdentity alpha c hab (curveCompactPath hp hab)
      (zeroSource a b)) (η : TimeTest) (hη : tsupport η ⊆ Set.Ioo a b)
    (φ : Test) (hφ : HasCompactSupport φ) :
    (∫ t in Set.Icc a b, weakOperator (fun s => energyDistribution (p s)) η φ t) =
      -(∫ t in Set.Icc a b, η t * Lp.toTemperedDistribution
        ((actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath hp hab)).value t) φ) := by
  have h := hPDE η hη φ hφ
  have hN :
      (∫ t in Set.Icc a b, η t * Lp.toTemperedDistribution
        ((actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath hp hab)).value t) φ) =
      ∫ t in Set.Icc a b, η t * ∫ x, φ x * forcing alpha c
        (energyValue (extendEnergyPath hab (energyPath _ (curveCompactPath hp hab)) t)) x :=
    integral_congr_ae
      ((actualHartreeSourceL1_pair_ae hDensity hSob hH hab (curveCompactPath hp hab) φ).mono
        (fun t ht => congrArg (fun z : ℂ => η t * z) ht))
  rw [profileSum_zeroSource_pairIntegral, profileSum_compactPath_weakIntegral hp hab η φ,
    ← hN] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Algebraic compact-test assembly from the actual profile equations. This
helper retains compact spatial support for every nonlinear profile. Its public
consumer below produces all profile equations from the canonical trajectories. -/
theorem profileSum_compactPDE_of_profileIdentities (hDensity : OrdinaryH1Density)
    {K alpha c a b : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (q : ℝ → EnergyState) (p : ℕ → ℝ → EnergyState)
    (hq : CurveFinite q) (hp : ∀ j, CurveFinite (p j)) (J : ℕ)
    (r : EnergyState) (hab : a ≤ b)
    (hprofile : ∀ j, ForcedHartreeCompactTestIdentity alpha c hab
      (curveCompactPath (hp j) hab) (zeroSource a b))
    (heq : ∀ t, q t = (∑ j ∈ Finset.range J, p j t) +
      freeEnergyState hDensity hSob t r) :
    ForcedHartreeCompactTestIdentity alpha c hab (curveCompactPath hq hab)
      (compactResidualSource hDensity hSob hH q p hq hp J hab) := by
  intro η hη φ hφ
  let S (j : ℕ) := actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath (hp j) hab)
  let E := actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath hq hab)
  have hi (j : ℕ) : IntegrableOn
      (weakOperator (fun t => energyDistribution (p j t)) η φ) (Set.Icc a b) :=
    energy_weakOperator_integrable (p j) (hp j).continuous.continuousOn η φ
  have hf := originalFree_weakEquation hDensity hSob hgen hab r η hη φ
  have hfreeint : (∫ t in Set.Icc a b,
      weakOperator (fun s => energyDistribution (freeEnergyState hDensity hSob s r)) η φ t) = 0 := by
    simpa only [zero_apply, mul_zero, integral_zero] using hf.2.2
  have hj (j : ℕ) :
      (∫ t in Set.Icc a b, weakOperator (fun s => energyDistribution (p j s)) η φ t) =
      -(∫ t in Set.Icc a b, η t * Lp.toTemperedDistribution ((S j).value t) φ) :=
    profileSum_profileWeakIntegral hDensity hSob hH (hp j) hab (hprofile j) η hη φ hφ
  have hpoint (t : ℝ) :
      weakOperator (fun s => energyDistribution (q s)) η φ t =
      (∑ j ∈ Finset.range J,
        weakOperator (fun s => energyDistribution (p j s)) η φ t) +
      weakOperator (fun s => energyDistribution (freeEnergyState hDensity hSob s r)) η φ t := by
    rw [show q = (fun s => (∑ j ∈ Finset.range J, p j s) +
        freeEnergyState hDensity hSob s r) from funext heq]
    rw [profileSum_weakOperator_add, profileSum_weakOperator_range]
  have hweak :
      (∫ t in Set.Icc a b, weakOperator (fun s => energyDistribution (q s)) η φ t) =
      -(∑ j ∈ Finset.range J,
        ∫ t in Set.Icc a b, η t * Lp.toTemperedDistribution ((S j).value t) φ) := by
    calc
      _ = ∫ t in Set.Icc a b,
          (∑ j ∈ Finset.range J,
            weakOperator (fun s => energyDistribution (p j s)) η φ t) +
          weakOperator (fun s => energyDistribution
            (freeEnergyState hDensity hSob s r)) η φ t :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = (∑ j ∈ Finset.range J,
          ∫ t in Set.Icc a b, weakOperator (fun s => energyDistribution (p j s)) η φ t) + 0 := by
        rw [integral_add (profileSum_integrable_range _ hi J) hf.1,
          profileSum_integral_range _ hi J, hfreeint]
      _ = _ := by simp only [hj, Finset.sum_neg_distrib, add_zero]
  have hN :
      (∫ t in Set.Icc a b, η t * Lp.toTemperedDistribution (E.value t) φ) =
      ∫ t in Set.Icc a b, η t * ∫ x, φ x * forcing alpha c
        (energyValue (extendEnergyPath hab (energyPath _ (curveCompactPath hq hab)) t)) x :=
    integral_congr_ae
      ((actualHartreeSourceL1_pair_ae hDensity hSob hH hab (curveCompactPath hq hab) φ).mono
        (fun t ht => congrArg (fun z : ℂ => η t * z) ht))
  have hres := sourceSubFold_pair_integral E S J η φ
  change _ = ∫ t in Set.Icc a b,
    η t * Lp.toTemperedDistribution ((sourceSubFold E S J).value t) φ
  rw [profileSum_compactPath_weakIntegral hq hab η φ, hweak, ← hN, hres]
  ring

/-- The literal finite framed nonlinear-profile sum plus the ORIGINAL free
remainder has the required forced compact PDE. No residual-PDE assumption and
no additional source, scalar-L2 or nonlinear-free hypothesis is accepted. -/
theorem actualProfileSum_compactPDE (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (s0 : ℕ → ℝ) (f : ℕ → EnergyState)
    (M : ∀ j, LocalMildTrajectory alpha c (s0 j) (f j))
    (hglobal : ∀ j, (M j).domain = Set.univ)
    (lambda : ℕ → ℝ) (hlambda : ∀ j, 0 < lambda j)
    (y : ℕ → Space) (tau : ℕ → ℝ)
    (q : ℝ → EnergyState) (hq : CurveFinite q)
    (hp : ∀ j, CurveFinite (stateFrame (M j).state (hlambda j) (y j) (tau j)))
    (J : ℕ) (r : EnergyState) (hab : a ≤ b)
    (heq : ∀ t, q t =
      (∑ j ∈ Finset.range J, stateFrame (M j).state (hlambda j) (y j) (tau j) t) +
        freeEnergyState hDensity hSob t r) :
    ForcedHartreeCompactTestIdentity alpha c hab (curveCompactPath hq hab)
      (compactResidualSource hDensity hSob hH q
        (fun j => stateFrame (M j).state (hlambda j) (y j) (tau j)) hq hp J hab) := by
  apply profileSum_compactPDE_of_profileIdentities hDensity hSob hH hgen q
    (fun j => stateFrame (M j).state (hlambda j) (y j) (tau j)) hq hp J r hab
  · intro j
    exact framedTrajectory_compactPDE hDensity hSob h0 hfree hret hH hgen
      (M j) (hglobal j) (hlambda j) (y j) (tau j) (hp j) hab
  · exact heq


/-- The R2 augmented curve, at the unchanged original depth and sequence index,
uses the very same residual source as the general finite-sum theorem. The Mj
can be instantiated directly with the marked actualMaximalTrajectory family. -/
theorem actual_augmented_compactPDE (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha c)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (s0 : ℕ → ℝ) (f : ℕ → EnergyState)
    (M : ∀ j, LocalMildTrajectory alpha c (s0 j) (f j))
    (hglobal : ∀ j, (M j).domain = Set.univ)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (J n : ℕ)
    (hq : CurveFinite (augmentedCurve hDensity hSob P u (fun j => (M j).state) J n))
    (hp : ∀ j, CurveFinite (nonlinearFrame P (fun j => (M j).state) j n))
    (hab : a ≤ b) :
    ForcedHartreeCompactTestIdentity alpha c hab (curveCompactPath hq hab)
      (compactResidualSource hDensity hSob hH
        (augmentedCurve hDensity hSob P u (fun j => (M j).state) J n)
        (fun j => nonlinearFrame P (fun j => (M j).state) j n) hq hp J hab) := by
  apply actualProfileSum_compactPDE hDensity hSob h0 hfree hret hH hgen s0 f M hglobal
    (fun j => P.scale j n) (fun j => P.scale_pos j n)
    (fun j => P.center j n) (fun j => P.time j n)
    (augmentedCurve hDensity hSob P u (fun j => (M j).state) J n) hq hp J
    (profileRemainder hDensity hSob P u J n) hab
  intro t
  simp only [augmentedCurve, Pi.add_apply, Finset.sum_apply, nonlinearFrame, freeCurve]

end HartreeF.FullResidual
