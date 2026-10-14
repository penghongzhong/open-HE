import FGeneralApproximationTransfer

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.GeneralProfileCross
open TimeHolder ProfileApproximation ProfileSpatialSmoothing CompactCross CrossContinuity CutoffApproximation ForcingDomain

def approximationPrecision (n : ℕ) : ℝ≥0 := ⟨cutoffScale n, (cutoffScale_pos n).le⟩

theorem approximationPrecision_coe (n : ℕ) :
    (approximationPrecision n : ℝ≥0∞) = smoothingPrecision n := by
  calc
    (approximationPrecision n : ℝ≥0∞) = ENNReal.ofReal (approximationPrecision n : ℝ) :=
      (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (approximationPrecision n : ℝ) = (approximationPrecision n : ℝ≥0∞)).symm
    _ = smoothingPrecision n := by rfl

/-- Uniform continuity error for any physical frames, with the common approximation
index fixed before either scale, translation, or time parameter. -/
theorem bounded_pair_frame_error {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {u h v k : ℝ → Space → ℂ} (A : ScalarCompactApproximation u h)
    (B : ScalarCompactApproximation v k) :
    ∃ C : ℝ≥0, ∀ n a b y z s r, 0 < a → 0 < b →
      forcingNorm (innerCross α c (seedFrame a y s (1/2) u) (seedFrame a y s (3/2) h)
        (seedFrame b z r (1/2) v) -
        innerCross α c (seedFrame a y s (1/2) (A.value n)) (seedFrame a y s (3/2) (A.gradient n))
          (seedFrame b z r (1/2) (B.value n))) ≤
        (C : ℝ≥0∞) * boundedModulus α (2*(A.bound+B.bound)) (smoothingPrecision n+smoothingPrecision n) ∧
      forcingNorm (outerCross α c (seedFrame a y s (1/2) u) (seedFrame b z r (1/2) v)
        (seedFrame b z r (3/2) k) -
        outerCross α c (seedFrame a y s (1/2) (A.value n)) (seedFrame b z r (1/2) (B.value n))
          (seedFrame b z r (3/2) (B.gradient n))) ≤
        (C : ℝ≥0∞) * boundedModulus α (2*(A.bound+B.bound)) (smoothingPrecision n+smoothingPrecision n) := by
  obtain ⟨C,hC⟩ := separate_cross_bounded_continuity hHLS
  refine ⟨C,?_⟩
  intro n a b y z s r ha hb
  have hAu := A.profile.frame ha y s
  have hAv := (A.approximate_profile n).frame ha y s
  have hBu := B.profile.frame hb z r
  have hBv := (B.approximate_profile n).frame hb z r
  have ht := hC _ _ _ _ _ _ _ _ (hAu.jointInputs hAv hBu hBv)
    (hAu.sliceInputs hAv hBu hBv) (2*(A.bound+B.bound))
    (approximationPrecision n+approximationPrecision n)
  have hv : valueSize ∞ 6 (seedFrame a y s (1/2) u) (seedFrame a y s (1/2) (A.value n))
      (seedFrame b z r (1/2) v) (seedFrame b z r (1/2) (B.value n)) ≤
      ((2*(A.bound+B.bound) : ℝ≥0) : ℝ≥0∞) := by
    unfold valueSize
    rw [seedFrame_V_invariant ha y s u A.profile.value_joint.aestronglyMeasurable,
      seedFrame_V_invariant ha y s _ (A.approximate_profile n).value_joint.aestronglyMeasurable,
      seedFrame_V_invariant hb z r v B.profile.value_joint.aestronglyMeasurable,
      seedFrame_V_invariant hb z r _ (B.approximate_profile n).value_joint.aestronglyMeasurable]
    calc
      _ ≤ ((A.bound : ℝ≥0∞)+A.bound)+(B.bound+B.bound) :=
        add_le_add (add_le_add A.value_V_bound (A.approximate_V_bound n))
          (add_le_add B.value_V_bound (B.approximate_V_bound n))
      _ = _ := by push_cast; ring
  have hs : valueSize 10 10 (seedFrame a y s (1/2) u) (seedFrame a y s (1/2) (A.value n))
      (seedFrame b z r (1/2) v) (seedFrame b z r (1/2) (B.value n)) ≤
      ((2*(A.bound+B.bound) : ℝ≥0) : ℝ≥0∞) := by
    unfold valueSize
    rw [seedFrame_S_invariant ha y s u A.profile.value_joint.aestronglyMeasurable,
      seedFrame_S_invariant ha y s _ (A.approximate_profile n).value_joint.aestronglyMeasurable,
      seedFrame_S_invariant hb z r v B.profile.value_joint.aestronglyMeasurable,
      seedFrame_S_invariant hb z r _ (B.approximate_profile n).value_joint.aestronglyMeasurable]
    calc
      _ ≤ ((A.bound : ℝ≥0∞)+A.bound)+(B.bound+B.bound) :=
        add_le_add (add_le_add A.value_S_bound (A.approximate_S_bound n))
          (add_le_add B.value_S_bound (B.approximate_S_bound n))
      _ = _ := by push_cast; ring
  have hw : referenceSize (seedFrame a y s (3/2) (A.gradient n))
      (seedFrame b z r (3/2) (B.gradient n)) ≤ ((2*(A.bound+B.bound) : ℝ≥0) : ℝ≥0∞) := by
    unfold referenceSize
    rw [seedFrame_W_invariant ha y s _ (A.approximate_profile n).gradient_joint.aestronglyMeasurable,
      seedFrame_W_invariant hb z r _ (B.approximate_profile n).gradient_joint.aestronglyMeasurable]
    calc
      _ ≤ (A.bound : ℝ≥0∞)+B.bound := add_le_add (A.approximate_W_bound n) (B.approximate_W_bound n)
      _ ≤ ((A.bound : ℝ≥0∞)+B.bound)+((A.bound : ℝ≥0∞)+B.bound) := le_add_right le_rfl
      _ = _ := by push_cast; ring
  have hds : changeSize 10 10 (seedFrame a y s (1/2) u) (seedFrame a y s (1/2) (A.value n))
      (seedFrame b z r (1/2) v) (seedFrame b z r (1/2) (B.value n)) ≤
      ((approximationPrecision n+approximationPrecision n : ℝ≥0) : ℝ≥0∞) := by
    unfold changeSize
    rw [show seedFrame a y s (1/2) u - seedFrame a y s (1/2) (A.value n) =
      (fun t x => seedFrame a y s (1/2) u t x - seedFrame a y s (1/2) (A.value n) t x) by rfl,
      show seedFrame b z r (1/2) v - seedFrame b z r (1/2) (B.value n) =
      (fun t x => seedFrame b z r (1/2) v t x - seedFrame b z r (1/2) (B.value n) t x) by rfl]
    rw [seedFrame_S_error ha y s u A.profile.value_joint.aestronglyMeasurable _
      (A.approximate_profile n).value_joint.aestronglyMeasurable,
      seedFrame_S_error hb z r v B.profile.value_joint.aestronglyMeasurable _
      (B.approximate_profile n).value_joint.aestronglyMeasurable,
      ENNReal.coe_add, approximationPrecision_coe]
    exact add_le_add (A.value_error n) (B.value_error n)
  have hdw : changeSize 10 (ENNReal.ofReal (30/13 : ℝ))
      (seedFrame a y s (3/2) h) (seedFrame a y s (3/2) (A.gradient n))
      (seedFrame b z r (3/2) k) (seedFrame b z r (3/2) (B.gradient n)) ≤
      ((approximationPrecision n+approximationPrecision n : ℝ≥0) : ℝ≥0∞) := by
    unfold changeSize
    rw [show seedFrame a y s (3/2) h - seedFrame a y s (3/2) (A.gradient n) =
      (fun t x => seedFrame a y s (3/2) h t x - seedFrame a y s (3/2) (A.gradient n) t x) by rfl,
      show seedFrame b z r (3/2) k - seedFrame b z r (3/2) (B.gradient n) =
      (fun t x => seedFrame b z r (3/2) k t x - seedFrame b z r (3/2) (B.gradient n) t x) by rfl]
    rw [seedFrame_W_error ha y s h A.profile.gradient_joint.aestronglyMeasurable _
      (A.approximate_profile n).gradient_joint.aestronglyMeasurable,
      seedFrame_W_error hb z r k B.profile.gradient_joint.aestronglyMeasurable _
      (B.approximate_profile n).gradient_joint.aestronglyMeasurable,
      ENNReal.coe_add, approximationPrecision_coe]
    exact add_le_add (A.gradient_error n) (B.gradient_error n)
  obtain ⟨_,_,hi,ho⟩ := ht hv hs hw hds hdw
  simpa only [ENNReal.coe_add, approximationPrecision_coe] using And.intro hi ho

#print axioms bounded_pair_frame_error
end HartreeF.GeneralProfileCross
