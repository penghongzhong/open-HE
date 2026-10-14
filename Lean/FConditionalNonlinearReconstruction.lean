import FActualSelectedFullResidual
import FActualProfileSumPDE
import FIndependentEssentialGlobalConsumer

/-! Conditional nonlinear reconstruction for the original canonical family.
All residual and compact-source/PDE inputs are produced from the actual
finite family. Large-profile finite X remains the explicit induction premise.
Author source, UNCOMPILED; no critical-element conclusion is asserted. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ConditionalNonlinearReconstruction
open EnergySpace SobolevStretch StationarySelfTest TimeHolder ProfileEnergy
  Retarded ActualStrichartz EndpointOutput ForcingDomain MaximalTrajectory
  CountableNonlinearProfiles CriticalTimeSobolev GeneralProfileCross
  R2Global R2Frames R2SquareTail R2FamilyTail R2TailForcing ActualR2Tail FullResidual
  CriticalPathSpace ActualDuhamelPath RawStabilityInputs
  HomogeneousStability IntervalNormExhaustion IndependentGlobalNormBridge
  HartreeDistributionalBridge LinearWeakEquation CriticalUniqueness
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace

local instance : SecondCountableTopologyEither ℝ EnergyState :=
  ⟨Or.inl inferInstance⟩

/-- A genuine whole-line paper realization supplies the three X domains of
that same continuous state curve. It is not merely a bound on a formal norm. -/
theorem curveFinite_of_paper_realization {d : ℝ → EnergyState} {C : ℝ}
    (hd : Continuous d) (h : ActualPaperRealization univ d C) : CurveFinite d := by
  have bound {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
      (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
      (g : ℝ → X → E) (hg : ActualNestedLpBound ν p r univ g C) :
      mixedNorm volume ν p r g ≤ ENNReal.ofReal C := by
    obtain ⟨F, hF, hFa, _⟩ := hg
    simpa only [Measure.restrict_univ] using
      actual_mixedNorm_le_of_global_nestedLp ν p r univ F g hF hFa
  let : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩
  refine ⟨hd, ?_, ?_, ?_⟩
  · rw [curveEnergy_eq_actual d hd]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (bound volume ∞ 2 _ h.1)
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (bound volume 10 10 _ h.2.2.2)
  · rw [curveW_eq_actual]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (bound volume 10 criticalExponent _ h.2.1)

/-- Reassembly is at the state level, after both genuine mixed domains have
been obtained. In particular the original solution has finite global S. -/
theorem curveFinite_of_difference_realization {v q : ℝ → EnergyState} {C : ℝ}
    (hv : Continuous v) (hq : CurveFinite q)
    (h : ActualPaperRealization univ (fun t => v t - q t) C) : CurveFinite v := by
  have hd : CurveFinite (v-q) :=
    curveFinite_of_paper_realization (hv.sub hq.continuous) h
  have he : (v-q)+q = v := sub_add_cancel v q
  exact he ▸ hd.add hq

/-- The stability tolerance is chosen after its constants and before any
profile depth or compact interval. No division by a zero constant occurs. -/
private theorem exists_stability_tolerance {ε ε0 C : ℝ}
    (hε : 0 < ε) (hε0 : 0 < ε0) (hC : 0 < C) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ε0 ∧ C*η ≤ ε := by
  refine ⟨min ε0 (ε/(C+1)), lt_min hε0 (div_pos hε (by positivity)),
    min_le_left _ _, ?_⟩
  have hd := min_le_right ε0 (ε/(C+1))
  calc
    C * min ε0 (ε/(C+1)) ≤ C*(ε/(C+1)) := mul_le_mul_of_nonneg_left hd hC.le
    _ ≤ (C+1)*(ε/(C+1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hε.le (by positivity))
    _ = ε := mul_div_cancel₀ ε (by positivity : C+1 ≠ 0)

private theorem paper_realization_mono {I : Set ℝ} {d : ℝ → EnergyState}
    {C D : ℝ} (hCD : C ≤ D) (h : ActualPaperRealization I d C) :
    ActualPaperRealization I d D := by
  have mono {X E : Type} [MeasurableSpace X] [NormedAddCommGroup E]
      (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)]
      (g : ℝ → X → E) (hg : ActualNestedLpBound ν p r I g C) :
      ActualNestedLpBound ν p r I g D := by
    obtain ⟨F, hF, hFa, hFz⟩ := hg
    exact ⟨F, hF.trans hCD, hFa, hFz⟩
  let : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩
  exact ⟨mono volume ∞ 2 _ h.1, mono volume 10 criticalExponent _ h.2.1,
    mono volume 2 6 _ h.2.2.1, mono volume 10 10 _ h.2.2.2⟩

/-- Conditional nonlinear reconstruction on the original sequence. The only
nonlinear induction input is global finite X for profiles above δ. The same
actual R2 producer discharges the small and zero profiles; four-slot residuals,
initial matching, compact source and compact PDE are all produced internally.
The original J is retained after extraction, and stability constants precede ε,
J, n and every compact window. -/
theorem exists_conditional_nonlinear_reconstruction (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre α c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS α c)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (cutoff : Highpass.Cutoff) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (P : LinearProfileFamily) (u : ℕ → EnergyState) (B : ℝ),
        (∀ n, pureGradientNorm (u n) ≤ B) →
        LinearProfileProperties hDensity hSob u P →
        ∀ (T : ℕ → ℝ) (f : ℕ → EnergyState),
          ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hH
            P T f →
          (∀ j, δ < actualProfileSize P j →
            let Mj := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
              (T j) (f j)
            Mj.domain = univ ∧ CurveFinite Mj.state) →
          let Mj := fun j => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
            (T j) (f j)
          let g := fun j => (Mj j).state
          (∀ j, (Mj j).domain = univ) ∧
          ∃ M : ℝ, 1 ≤ M ∧
            (∀ J n, CurveFinite (augmentedCurve hDensity hSob P u g J n) ∧
              xNorm (augmentedCurve hDensity hSob P u g J n) ≤ M) ∧
            ∀ ε : ℝ, 0 < ε → ∃ J N : ℕ,
              (P.count = ⊤ ∨ P.count = (J : WithTop ℕ)) ∧
              ∀ n ≥ N,
                let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
                  0 (u n)
                let v := augmentedCurve hDensity hSob P u g J n
                U.domain = univ ∧ CurveFinite U.state ∧
                  ActualPaperRealization univ (fun t => U.state t-v t) ε ∧
                  actualPaperDifferenceSize univ U.state v ≤ ENNReal.ofReal ε ∧
                  ∀ t : ℝ, pureGradientNorm (U.state t-v t) ≤ ε := by
  obtain ⟨δ, Csd, Ccorr, Cforce, Cf, hδ, _hCsd, hCcorr, hCforce, hCf, hR2⟩ :=
    exists_actual_nonlinear_R2_tail hDensity hSob h0 hfree hret hefree heret hH
  refine ⟨δ, hδ, ?_⟩
  intro P u B hB hp T f hmatch hlarge
  let Mj := fun j => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
    (T j) (f j)
  let g := fun j => (Mj j).state
  obtain ⟨hglobal, L0, M, rp, htail⟩ := hR2 P u B hB hp T f hmatch hlarge
  have hM : 0 ≤ M := le_trans (by norm_num) htail.cap_one
  have hframe (j n : ℕ) : CurveFinite (nonlinearFrame P g j n) :=
    CurveFinite.stateFrame (htail.curve_finite j) (P.scale_pos j n) (P.center j n) (P.time j n)
  let rq (J n : ℕ) : EnergyJointFields volume (augmentedCurve hDensity hSob P u g J n) :=
    energyJointFields volume (augmentedCurve hDensity hSob P u g J n)
      (htail.augmented J n).1.continuous.aestronglyMeasurable
  obtain ⟨ε0, C, hε0, _hε01, hC, hstab⟩ :=
    exists_essential_input_global_stability hDensity hSob h0 hfree hret hefree heret hH
      hgen hUnique hM hM
  refine ⟨hglobal, M, htail.cap_one, htail.augmented, ?_⟩
  intro ε hε
  obtain ⟨η, hη, hη0, hCη⟩ := exists_stability_tolerance hε hε0 hC
  obtain ⟨J, N, helig, hn⟩ := actual_selected_full_residual
    hDensity hSob h0 hfree hret hefree heret hH cutoff
    P u hB hp T f hmatch δ Csd Ccorr Cforce Cf L0 M hCcorr hCforce hCf rp htail rq η hη
  refine ⟨J, N, helig, ?_⟩
  intro n hnN
  let v := augmentedCurve hDensity hSob P u g J n
  have hv : CurveFinite v := (htail.augmented J n).1
  have hvM : xNorm v ≤ M := (htail.augmented J n).2
  let p := fun j => nonlinearFrame P g j n
  have hp' : ∀ j, CurveFinite (p j) := fun j => hframe j n
  let Q : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ univ →
      CriticalPath (intervalMeasure a b) := fun hab _ => curveCompactPath hv hab
  let E : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ univ →
      CompatibleL1IntervalSource a b := fun hab _ =>
        compactResidualSource hDensity hSob hH v p hv hp' J hab
  have hQ : ∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ univ) (t : Icc a b),
      energyPath _ (Q hab hsub) t = v t := fun hab _ t => curveCompactPath_energy hv hab t
  have hPDE : ∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ univ),
      ForcedHartreeCompactTestIdentity α c hab (Q hab hsub) (E hab hsub) := by
    intro a b hab hsub
    exact actual_augmented_compactPDE hDensity hSob h0 hfree hret hH hgen
      T f Mj hglobal P u J n hv hp' hab
  have herr : ∀ {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ univ),
      (E hab hsub).paperForcingSize ≤ ENNReal.ofReal η := by
    intro a b hab hsub
    exact (compactResidualSource_paperForcingSize_le hDensity hSob hH
      v p hv hp' (rq J n) (fun j => rp j n) J hab).trans (hn n hnN).1
  have hresult := hstab univ ordConnected_univ
    (show ∃ l ∈ (univ : Set ℝ), ∃ r ∈ (univ : Set ℝ), l < r from
      ⟨0, mem_univ _, 1, mem_univ _, by norm_num⟩)
    (s := 0) (epsilon := η) (mem_univ _) (u n) v Q E hQ hPDE
    (fun hab _ => curveCompactPath_energy_cap hv hvM hab.le)
    (fun hab _ => curveCompactPath_value_cap hv hvM hab)
    herr hη.le hη0 (hn n hnN).2
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (u n)
  have hU : U.domain = univ := subset_antisymm (subset_univ _) hresult.1
  have hUcont : Continuous U.state := continuousOn_univ.mp (hU ▸ U.continuous)
  refine ⟨hU, curveFinite_of_difference_realization hUcont hv hresult.2.1,
    paper_realization_mono hCη hresult.2.1,
    hresult.2.2.1.trans (ENNReal.ofReal_le_ofReal hCη), ?_⟩
  intro t
  exact (hresult.2.2.2 t (mem_univ _)).trans hCη

end HartreeF.ConditionalNonlinearReconstruction
