import FActualResidualDomains
import FRawStabilityInputAssembly
import FL1RetardedSubtraction
import FEndpointSourceWeakDerivative

/-! The actual residual source on a compact interval.  The scalar source is
constructed in the existing compatible L1 graph, by a finite subtraction fold.
Its gradient is then identified with the SAME global residual candidate through
genuine weak gradients and tempered-distribution uniqueness.  Author source;
UNCOMPILED.  No scalar spacetime measurability or scalar time-L2 premise. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal NNReal Topology
namespace HartreeF.FullResidual
open EnergySpace SobolevStretch StationarySelfTest TimeHolder ForcingDomain
  CriticalTimeSobolev CriticalPathSpace IntervalTimeTransport ActualDuhamelPath
  Retarded R2Global R2TailForcing RawStabilityInputs HartreeDistributionalBridge
  WeakHartreeProduct ProfileSpatialSmoothing ProfileApproximation GeneralProfileCross
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath

/-- Global finite X supplies the existing local critical-path producer.  The
subtype interval measure is transported to restricted real time explicitly. -/
def curveLocallyCritical {q : ℝ → EnergyState} (hq : CurveFinite q) :
    LocallyCriticalEnergyCurve Set.univ q where
  continuousOn := hq.continuous.continuousOn
  localW := by
    intro a b hab hI
    apply ne_top_of_le_ne_top (by simpa only [curveW_eq_actual] using hq.gradient)
    simpa only [Measure.restrict_univ] using
      (compact_mixedNorm_le_restrict hI 10 criticalExponent
        (fun t => energyComplexGradient (q t)))

def curveCompactPath {q : ℝ → EnergyState} (hq : CurveFinite q)
    {a b : ℝ} (hab : a ≤ b) : CriticalPath (intervalMeasure a b) :=
  (curveLocallyCritical hq).compactPath hab (Set.subset_univ _)

@[simp] theorem curveCompactPath_energy {q : ℝ → EnergyState} (hq : CurveFinite q)
    {a b : ℝ} (hab : a ≤ b) (t : Set.Icc a b) :
    energyPath _ (curveCompactPath hq hab) t = q t := rfl

theorem curveCompactPath_extend_eq {q : ℝ → EnergyState} (hq : CurveFinite q)
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    extendEnergyPath hab (energyPath _ (curveCompactPath hq hab)) t = q t :=
  (extendEnergyPath_val hab (energyPath _ (curveCompactPath hq hab)) ⟨t, ht⟩).trans
    (curveCompactPath_energy hq hab ⟨t, ht⟩)

theorem curveCompactPath_energy_mixed_le {q : ℝ → EnergyState} (hq : CurveFinite q)
    {a b : ℝ} (hab : a ≤ b) :
    mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ (curveCompactPath hq hab) t)) ≤
        curveEnergy q := by
  rw [curveEnergy_eq_actual q hq.continuous]
  simpa only [curveCompactPath_energy, Measure.restrict_univ] using
    (compact_mixedNorm_le_restrict (Set.subset_univ (Set.Icc a b)) ∞ 2
      (fun t => energyComplexGradient (q t)))

theorem curveCompactPath_value_mixed_le {q : ℝ → EnergyState} (hq : CurveFinite q)
    {a b : ℝ} (hab : a ≤ b) :
    mixedNorm (intervalMeasure a b) volume 10 10
      (fun t => energyValue (energyPath _ (curveCompactPath hq hab) t)) ≤ curveS q := by
  simpa only [curveCompactPath_energy, Measure.restrict_univ, curveS,
    stateValueField] using
    (compact_mixedNorm_le_restrict (Set.subset_univ (Set.Icc a b)) 10 10
      (fun t => energyValue (q t)))

theorem curveCompactPath_energy_cap {q : ℝ → EnergyState} (hq : CurveFinite q)
    {M a b : ℝ} (hM : xNorm q ≤ M) (hab : a ≤ b) :
    mixedNorm (intervalMeasure a b) volume ∞ 2
      (fun t => energyComplexGradient (energyPath _ (curveCompactPath hq hab) t)) ≤
        ENNReal.ofReal M := by
  apply (curveCompactPath_energy_mixed_le hq hab).trans
  apply (curveEnergy_le_curveX q).trans
  rw [← ofReal_xNorm hq]
  exact ENNReal.ofReal_le_ofReal hM

theorem curveCompactPath_value_cap {q : ℝ → EnergyState} (hq : CurveFinite q)
    {M a b : ℝ} (hM : xNorm q ≤ M) (hab : a ≤ b) :
    mixedNorm (intervalMeasure a b) volume 10 10
      (fun t => energyValue (energyPath _ (curveCompactPath hq hab) t)) ≤
        ENNReal.ofReal M := by
  apply (curveCompactPath_value_mixed_le hq hab).trans
  apply (curveS_le_curveX q).trans
  rw [← ofReal_xNorm hq]
  exact ENNReal.ofReal_le_ofReal hM

/-- An explicit subtraction fold.  This requires no Add, Zero or Finset-sum
instance on CompatibleL1IntervalSource. -/
def sourceSubFold {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (S : ℕ → CompatibleL1IntervalSource a b) : ℕ → CompatibleL1IntervalSource a b
  | 0 => E
  | J + 1 => (sourceSubFold E S J).sub (S J)

theorem sourceSubFold_distribution_ae {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (S : ℕ → CompatibleL1IntervalSource a b) (J : ℕ) :
    ∀ᵐ t ∂localMeasure a b,
      Lp.toTemperedDistribution ((sourceSubFold E S J).value t) =
        Lp.toTemperedDistribution (E.value t) -
          ∑ j ∈ Finset.range J, Lp.toTemperedDistribution ((S j).value t) := by
  induction J with
  | zero =>
      filter_upwards [] with t
      simp only [sourceSubFold, Finset.range_zero, Finset.sum_empty, sub_zero]
  | succ J ih =>
      filter_upwards [(sourceSubFold E S J).sub_distribution_ae (S J), ih] with t ht hi
      change Lp.toTemperedDistribution (((sourceSubFold E S J).sub (S J)).value t) = _
      rw [ht, hi, Finset.sum_range_succ]
      abel

/-- Both quotient levels are handled by their AE subtraction equations. -/
theorem sourceSubFold_value_ae {a b : ℝ} (E : CompatibleL1IntervalSource a b)
    (S : ℕ → CompatibleL1IntervalSource a b) (J : ℕ) :
    ∀ᵐ t ∂localMeasure a b,
      ((sourceSubFold E S J).value t : Space → ℂ) =ᵐ[volume]
        (fun x => E.value t x - ∑ j ∈ Finset.range J, (S j).value t x) := by
  induction J with
  | zero =>
      filter_upwards [] with t
      simp only [sourceSubFold, Finset.range_zero, Finset.sum_empty, sub_zero]
      exact Filter.EventuallyEq.rfl
  | succ J ih =>
      filter_upwards [(sourceSubFold E S J).sub_value_ae (S J), ih] with t ht hi
      change (((sourceSubFold E S J).sub (S J)).value t : Space → ℂ) =ᵐ[volume] _
      rw [ht]
      filter_upwards [Lp.coeFn_sub ((sourceSubFold E S J).value t) ((S J).value t), hi]
        with x hx hix
      rw [hx, Pi.sub_apply, hix, Finset.sum_range_succ]
      ring

variable (hDensity : OrdinaryH1Density) {K α c : ℝ}
  (hSob : OrdinarySobolev K) (hH : OrdinaryHLS α c)

def compactResidualSource (q : ℝ → EnergyState) (p : ℕ → ℝ → EnergyState)
    (hq : CurveFinite q) (hp : ∀ j, CurveFinite (p j)) (J : ℕ)
    {a b : ℝ} (hab : a ≤ b) : CompatibleL1IntervalSource a b :=
  sourceSubFold (actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath hq hab))
    (fun j => actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath (hp j) hab)) J

theorem curveHartreeSource_value_ae {q : ℝ → EnergyState} (hq : CurveFinite q)
    {a b : ℝ} (hab : a ≤ b) :
    ∀ᵐ t ∂localMeasure a b,
      ((actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath hq hab)).value t :
        Space → ℂ) =ᵐ[volume] forcing α c (energyValue (q t)) := by
  filter_upwards [actualHartreeSourceL1_value_ae hDensity hSob hH hab
    (curveCompactPath hq hab), ae_restrict_mem measurableSet_Icc] with t ht htm
  simpa only [curveCompactPath_extend_eq hq hab t htm] using ht

/-- The native L1 source value is the literal full scalar residual. -/
theorem compactResidualSource_value_ae (q : ℝ → EnergyState) (p : ℕ → ℝ → EnergyState)
    (hq : CurveFinite q) (hp : ∀ j, CurveFinite (p j)) (J : ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    ∀ᵐ t ∂localMeasure a b,
      ((compactResidualSource hDensity hSob hH q p hq hp J hab).value t : Space → ℂ)
        =ᵐ[volume] literalResidual (Finset.range J) α c q p t := by
  have hprofiles := (eventually_all_finset (Finset.range J)).2
    (fun j _ => curveHartreeSource_value_ae hDensity hSob hH (hp j) hab)
  filter_upwards [sourceSubFold_value_ae
    (actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath hq hab))
    (fun j => actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath (hp j) hab)) J,
    curveHartreeSource_value_ae hDensity hSob hH hq hab, hprofiles] with t ht hqv hpv
  filter_upwards [ht, hqv, (eventually_all_finset (Finset.range J)).2 hpv] with x hx hqx hpx
  change (compactResidualSource hDensity hSob hH q p hq hp J hab).value t x = _
  rw [show (compactResidualSource hDensity hSob hH q p hq hp J hab).value t x =
    (actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath hq hab)).value t x -
      ∑ j ∈ Finset.range J,
        (actualHartreeSourceL1 hDensity hSob hH hab (curveCompactPath (hp j) hab)).value t x
    from hx]
  unfold literalResidual
  rw [hqx]
  congr 1
  exact Finset.sum_congr rfl hpx

theorem compactResidualSource_pair_ae (q : ℝ → EnergyState) (p : ℕ → ℝ → EnergyState)
    (hq : CurveFinite q) (hp : ∀ j, CurveFinite (p j)) (J : ℕ)
    {a b : ℝ} (hab : a ≤ b) (φ : Test) :
    (fun t => Lp.toTemperedDistribution
      ((compactResidualSource hDensity hSob hH q p hq hp J hab).value t) φ)
      =ᵐ[localMeasure a b]
        (fun t => ∫ x, φ x * literalResidual (Finset.range J) α c q p t x) := by
  filter_upwards [compactResidualSource_value_ae hDensity hSob hH q p hq hp J hab]
    with t ht
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  simp only [hx, smul_eq_mul]

omit hDensity hSob hH in
/-- Uniqueness of the actual spatial gradient of an already-produced compatible
source.  The endpoint weak-derivative theorem first proves both Schwartz-test
integrability domains from the actual spatial Lp classes, then invokes genuine
weak_gradient_tempered_derivative.  Its TD equality is compared with E.derivative.
Only the vector, never the scalar forcing, needs global joint measurability. -/
theorem compatibleSource_vector_ae_of_weak {a b : ℝ}
    (E : CompatibleL1IntervalSource a b) (e : ℝ → Space → ℂ)
    (G : ℝ → Space → EuclideanSpace ℂ (Fin 3))
    (he : ∀ᵐ t ∂localMeasure a b, (E.value t : Space → ℂ) =ᵐ[volume] e t)
    (hjoint : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2)
      (volume.prod volume))
    (hfinite : mixedNorm volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) G ≠ ∞)
    (hweak : ∀ᵐ t ∂(volume : Measure ℝ),
      HasWeakGradient (fun x => (e t x).re) (fun x => gradientReal (G t x)) ∧
      HasWeakGradient (fun x => (e t x).im) (fun x => gradientImag (G t x))) :
    ∀ᵐ t ∂localMeasure a b, E.complexGradient t =ᵐ[volume] G t := by
  letI : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
  letI : Fact (ENNReal.ofReal (6/5 : ℝ) ≠ ∞) := ⟨ENNReal.ofReal_ne_top⟩
  have hμ : localMeasure a b ≤ (volume : Measure ℝ) := Measure.restrict_le_self
  have hj := hjoint.mono_measure (Measure.prod_mono hμ le_rfl)
  have hf : mixedNorm (localMeasure a b) volume 2 (ENNReal.ofReal (6/5 : ℝ)) G ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (eLpNorm_mono_measure _ hμ)
  have hs : ∀ᵐ t ∂localMeasure a b,
      MemLp (G t) (ENNReal.ofReal (6/5 : ℝ)) volume :=
    finite_mixedNorm_ae_slice_memLp _ volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (by norm_num) (by norm_num) G hf
  let H := jointLpRealization (localMeasure a b) volume 2 (ENNReal.ofReal (6/5 : ℝ))
    (fun z : ℝ × Space => G z.1 z.2) hj hs hf
  have hH : ∀ᵐ t ∂localMeasure a b,
      (H t : Space → EuclideanSpace ℂ (Fin 3)) =ᵐ[volume] G t :=
    jointLpRealization_coeFn _ _ _ _ _ _ _ _
  filter_upwards [E.derivative, he, hH, ae_mono hμ hweak] with t hEt het hHt hwt
  have hR : HasWeakGradient (fun x => (e t x).re) (fun x => gradientReal (H t x)) :=
    weakGradient_congr_fields hwt.1 Filter.EventuallyEq.rfl
      (hHt.symm.mono fun x hx => congrArg gradientReal hx)
  have hI : HasWeakGradient (fun x => (e t x).im) (fun x => gradientImag (H t x)) :=
    weakGradient_congr_fields hwt.2 Filter.EventuallyEq.rfl
      (hHt.symm.mono fun x hx => congrArg gradientImag hx)
  have hc (j : Fin 3) : (E.gradient j t : Space → ℂ) =ᵐ[volume]
      fun x => H t x j := by
    have hd := endpointSource_weakDerivative_of_weakGradients (E.value t) (H t)
      (e t) het hR hI j
    exact (spatial_ae_eq_of_distribution_eq (E.gradient j t)
      (endpointGradientCoordinate j (H t)) ((hEt j).symm.trans hd)).trans
      (endpointGradientCoordinate_coeFn j (H t))
  filter_upwards [ae_all_iff.mpr hc, hHt] with x hx hGx
  apply Eq.trans _ hGx
  exact PiLp.ext fun j => hx j

theorem compactResidualSource_gradient_ae (q : ℝ → EnergyState)
    (p : ℕ → ℝ → EnergyState) (hq : CurveFinite q) (hp : ∀ j, CurveFinite (p j))
    (rq : EnergyJointFields volume q) (rp : ∀ j, EnergyJointFields volume (p j))
    (J : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∀ᵐ t ∂localMeasure a b,
      (compactResidualSource hDensity hSob hH q p hq hp J hab).complexGradient t =ᵐ[volume]
        residualCandidate (Finset.range J) α c rq rp t := by
  have hd := actual_residual_domains hDensity hSob hH (Finset.range J) q p hq
    (fun j _ => hp j) rq rp
  exact compatibleSource_vector_ae_of_weak _ _ _
    (compactResidualSource_value_ae hDensity hSob hH q p hq hp J hab)
    hd.candidate_joint hd.candidate_finite hd.candidate_weak

/-- This is equality of the complex Euclidean vector norms, with constant one.
No coordinate l1, Pi maximum or separately bounded majorant replaces the vector. -/
theorem compactResidualSource_paperForcingSize (q : ℝ → EnergyState)
    (p : ℕ → ℝ → EnergyState) (hq : CurveFinite q) (hp : ∀ j, CurveFinite (p j))
    (rq : EnergyJointFields volume q) (rp : ∀ j, EnergyJointFields volume (p j))
    (J : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (compactResidualSource hDensity hSob hH q p hq hp J hab).paperForcingSize =
      mixedNorm (localMeasure a b) volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (residualCandidate (Finset.range J) α c rq rp) := by
  apply eLpNorm_congr_ae
  filter_upwards [compactResidualSource_gradient_ae hDensity hSob hH q p hq hp rq rp J hab]
    with t ht
  exact eLpNorm_congr_ae ht

theorem compactResidualSource_paperForcingSize_le (q : ℝ → EnergyState)
    (p : ℕ → ℝ → EnergyState) (hq : CurveFinite q) (hp : ∀ j, CurveFinite (p j))
    (rq : EnergyJointFields volume q) (rp : ∀ j, EnergyJointFields volume (p j))
    (J : ℕ) {a b : ℝ} (hab : a ≤ b) :
    (compactResidualSource hDensity hSob hH q p hq hp J hab).paperForcingSize ≤
      mixedNorm volume volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (residualCandidate (Finset.range J) α c rq rp) := by
  rw [compactResidualSource_paperForcingSize hDensity hSob hH q p hq hp rq rp J hab]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

end HartreeF.FullResidual
