import FR2SameCanonicalSmallProfiles
import FR2FamilyTailAlgebra
import FCountableActualNonlinearProfiles

/-! Actual R2 tail for the original matching-sequence canonical family.
Small-profile globality, correction and source domains are produced. Only
nonsmall profiles retain the explicit global finite-X induction premise.
No complete residual, forced-PDE reconstruction or critical element is asserted.
Static author source; every new declaration remains UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualR2Tail
open EnergySpace SobolevStretch StationarySelfTest TimeHolder ProfileEnergy
  Retarded ActualStrichartz EndpointOutput ForcingDomain MaximalTrajectory
  CountableNonlinearProfiles CriticalTimeSobolev GeneralProfileCross FreeValueGradient
  R2Global R2Frames R2SquareTail R2TailForcing R2FamilyTail

/-- Actual finite-tail conclusions on one given family and one fixed set of
joint representatives. All scalar and vector norms refer to the same curves. -/
structure TailBounds (hDensity : OrdinaryH1Density) {K α c : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) (δ Csd Ccorr Cforce Cf : ℝ) (L0 : ℕ) (M : ℝ)
    (r : ∀ j n, EnergyJointFields volume (nonlinearFrame P g j n)) : Prop where
  curve_finite : ∀ j, CurveFinite (g j)
  correction_finite : ∀ j, CurveFinite (normalizedCorrection hDensity hSob P g j)
  small_norm : ∀ j, actualProfileSize P j ≤ δ → xNorm (g j) ≤ Csd*actualProfileSize P j
  small_correction : ∀ j, actualProfileSize P j ≤ δ →
    xNorm (normalizedCorrection hDensity hSob P g j) ≤ Ccorr*actualProfileSize P j^(5+2*α)
  zero_profile : ∀ j, actualProfileSize P j = 0 → ∀ t, g j t = 0
  small_tail : ∀ j ≥ L0, actualProfileSize P j ≤ δ
  block : ∀ L ≥ L0, ∀ J, L ≤ J → (J : WithTop ℕ) ≤ P.count → ∀ η : ℝ, 0 < η →
    ∃ N : ℕ, ∀ n ≥ N,
      CurveFinite (nonlinearBlock P g L J n) ∧
      xNorm (nonlinearBlock P g L J n) ≤
        Cf*(actualProfileTail P L+η)+Ccorr*actualProfileTail P L^(5+2*α)
  source_domains : ∀ j n, ActualDefectDomains α c 0 (r j n).u 0 0 (r j n).U (r j n).V
  source_scalar_ae : ∀ j n, ∀ᵐ t ∂volume, literalForcing α c 0 (r j n).u t =ᵐ[volume]
    forcing α c (energyValue (nonlinearFrame P g j n t))
  source_small : ∀ j ≥ L0, ∀ n,
    vectorForcingNorm (sourceGradient α c (r j n)) ≤
      ENNReal.ofReal (Cforce*actualProfileSize P j^(5+2*α))
  source_tail : ∀ L ≥ L0, ∀ J n,
    vectorForcingNorm (fun t x => ∑ j ∈ Finset.Ico L J, sourceGradient α c (r j n) t x) ≠ ∞ ∧
    vectorForcingNorm (fun t x => ∑ j ∈ Finset.Ico L J, sourceGradient α c (r j n) t x) ≤
      ENNReal.ofReal (Cforce*actualProfileTail P L^(5+2*α))
  cap_one : 1 ≤ M
  augmented : ∀ J n, CurveFinite (augmentedCurve hDensity hSob P u g J n) ∧
    xNorm (augmentedCurve hDensity hSob P u g J n) ≤ M

private theorem freeCurve_bound (hDensity : OrdinaryH1Density) {K Ch : ℝ}
    (hSob : OrdinarySobolev K) (hfree : OrdinaryHomogeneousStrichartz Ch) (f : EnergyState) :
    CurveFinite (freeCurve hDensity hSob f) ∧
      xNorm (freeCurve hDensity hSob f) ≤ freeXConstant K Ch*pureGradientNorm f := by
  simpa only [anchoredFreeCurve, sub_zero, freeCurve] using
    anchoredFreeCurve_bound hDensity hSob hfree 0 f

/-- One set of constants precedes the selected linear and actual nonlinear
families. The only nonlinear induction input concerns δ<a_j. Every small and
zero label is discharged by the retained matching-sequence producer. -/
theorem exists_actual_nonlinear_R2_tail (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre α c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS α c) :
    ∃ δ Csd Ccorr Cforce Cf : ℝ,
      0 < δ ∧ 0 ≤ Csd ∧ 0 ≤ Ccorr ∧ 0 ≤ Cforce ∧ 0 ≤ Cf ∧
      ∀ (P : LinearProfileFamily) (u : ℕ → EnergyState) (B : ℝ),
        (∀ n, pureGradientNorm (u n) ≤ B) →
        LinearProfileProperties hDensity hSob u P → ∀ (T : ℕ → ℝ) (f : ℕ → EnergyState),
        ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hH P T f →
        (∀ j, δ < actualProfileSize P j →
          let Mj := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH (T j) (f j)
          Mj.domain = univ ∧ CurveFinite Mj.state) →
        let Mj := fun j => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH (T j) (f j)
        let g := fun j => (Mj j).state
        (∀ j, (Mj j).domain = univ) ∧
        ∃ L0 : ℕ, ∃ M : ℝ,
          ∃ r : ∀ j n, EnergyJointFields volume (nonlinearFrame P g j n),
            TailBounds (α := α) (c := c) hDensity hSob P u g δ Csd Ccorr Cforce Cf L0 M r := by
  obtain ⟨δ, Csd, Ccorr, hδ, hCsd, hCcorr, hsmall⟩ :=
    exists_same_canonical_small_profile_bounds hDensity hSob h0 hfree hret hefree heret hH
  obtain ⟨CF, hforce⟩ := exists_source_gradient_power_bound hDensity hSob hH
  let m : ℝ := 5+2*α
  let Cforce : ℝ := (CF : ℝ)*Csd^m
  let Cf : ℝ := freeXConstant K Ch
  have hm : 2 ≤ m := by dsimp [m]; linarith [hH.order_pos]
  have hCforce : 0 ≤ Cforce := mul_nonneg CF.coe_nonneg (Real.rpow_nonneg hCsd _)
  have hCf : 0 ≤ Cf := freeXConstant_nonneg hSob hfree
  refine ⟨δ, Csd, Ccorr, Cforce, Cf, hδ, hCsd, hCcorr, hCforce, hCf, ?_⟩
  intro P u B hB hp T f hmatch hlarge
  let Mj := fun j => actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH (T j) (f j)
  let g := fun j => (Mj j).state
  have hs (j : ℕ) (hj : actualProfileSize P j ≤ δ) :=
    hsmall (T j) (f j) (P.profile j) (P.time j) (hmatch j).1 (hmatch j).2 hj
  have hg (j : ℕ) : (Mj j).domain = univ ∧ CurveFinite (g j) := by
    by_cases hj : actualProfileSize P j ≤ δ
    · exact ⟨(hs j hj).1, (hs j hj).2.1⟩
    · exact hlarge j (lt_of_not_ge hj)
  have hfree' (v : EnergyState) : CurveFinite (freeCurve hDensity hSob v) ∧
      xNorm (freeCurve hDensity hSob v) ≤ Cf*pureGradientNorm v :=
    freeCurve_bound hDensity hSob hfree v
  have hc (j : ℕ) : CurveFinite (normalizedCorrection hDensity hSob P g j) :=
    (hg j).2.sub (hfree' (P.profile j)).1
  have hcorr (j : ℕ) (hj : actualProfileSize P j ≤ δ) :
      xNorm (normalizedCorrection hDensity hSob P g j) ≤ Ccorr*actualProfileSize P j^m := by
    simpa only [normalizedCorrection, freeCurve, anchoredFreeCurve, sub_zero,
      actualProfileSize, m] using (hs j hj).2.2.2.2.1
  obtain ⟨L0, hL0⟩ := actualProfileSize_eventually_le hDensity hSob P u hp hB hδ
  have htail := fun j hj => hcorr j (hL0 j hj)
  obtain ⟨M, hM, haug⟩ := exists_augmented_uniform_cap hDensity hSob P u hp hB g hc
    hCcorr hCf hm hfree' L0 htail
  have hframe (j n : ℕ) : CurveFinite (nonlinearFrame P g j n) :=
    CurveFinite.stateFrame (hg j).2 (P.scale_pos j n) (P.center j n) (P.time j n)
  let r (j n : ℕ) : EnergyJointFields volume (nonlinearFrame P g j n) :=
    energyJointFields volume (nonlinearFrame P g j n) (hframe j n).continuous.aestronglyMeasurable
  have hdomains (j n : ℕ) := source_domains hDensity hSob hH (hframe j n) (r j n)
  have hsource (j : ℕ) (hj : L0 ≤ j) (n : ℕ) :
      vectorForcingNorm (sourceGradient α c (r j n)) ≤
        ENNReal.ofReal (Cforce*actualProfileSize P j^m) := by
    have hx : xNorm (nonlinearFrame P g j n) ≤ Csd*actualProfileSize P j := by
      rw [nonlinearFrame, stateFrame_xNorm (hg j).2.continuous]
      exact (hs j (hL0 j hj)).2.2.1
    have hb := (hforce (nonlinearFrame P g j n) (hframe j n) (r j n)
      (Csd*actualProfileSize P j) (mul_nonneg hCsd (actualProfileSize_nonneg P j)) hx).2
    exact hb.trans_eq (by
      congr 1
      rw [Real.mul_rpow hCsd (actualProfileSize_nonneg P j)]
      dsimp [Cforce, m]
      ring)
  refine ⟨fun j => (hg j).1, L0, M, r, ?_⟩
  refine { curve_finite := fun j => (hg j).2
           correction_finite := hc
           small_norm := fun j hj => (hs j hj).2.2.1
           small_correction := hcorr
           zero_profile := ?_
           small_tail := hL0
           block := ?_
           source_domains := hdomains
           source_scalar_ae := fun j n => source_scalar_canonical_ae α c (r j n)
           source_small := hsource
           source_tail := ?_
           cap_one := hM
           augmented := haug }
  · intro j hz
    exact (hs j (by rw [hz]; exact hδ.le)).2.2.2.2.2.2 hz
  · intro L hL J hLJ hJ η hη
    exact nonlinear_block_eventual_bound hDensity hSob P u hp hB g hc hCcorr hCf hm hfree'
      hLJ hJ (fun j hj => hcorr j (hL0 j (hL.trans hj))) hη
  · intro L hL J n
    have hsum := source_gradient_sum_le hDensity hSob hH (Finset.Ico L J)
      (fun j => nonlinearFrame P g j n) (fun j _ => hframe j n) (fun j => r j n)
    refine ⟨source_gradient_sum_finite hDensity hSob hH (Finset.Ico L J)
      (fun j => nonlinearFrame P g j n) (fun j _ => hframe j n) (fun j => r j n), ?_⟩
    apply hsum.trans
    calc
      (∑ j ∈ Finset.Ico L J, vectorForcingNorm (sourceGradient α c (r j n))) ≤
          ∑ j ∈ Finset.Ico L J, ENNReal.ofReal (Cforce*actualProfileSize P j^m) :=
        Finset.sum_le_sum (fun j hj => hsource j (hL.trans (Finset.mem_Ico.mp hj).1) n)
      _ = ENNReal.ofReal (Cforce * ∑ j ∈ Finset.Ico L J, actualProfileSize P j^m) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ =>
          mul_nonneg hCforce (Real.rpow_nonneg (actualProfileSize_nonneg P j) _))]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (actualProfilePower_block_le_tail_rpow hDensity hSob P u hp hB hm L J) hCforce)

end HartreeF.ActualR2Tail
