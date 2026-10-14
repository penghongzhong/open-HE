import FLocalProductContinuity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.LocalProfileProducts
open TimeHolder ProfileApproximation ProfileSpatialSmoothing GeneralProfileCross CompactCross

/-- One finite coefficient controls P and Q errors uniformly over all physical frames.
The same approximation index n is chosen before either frame's parameters. -/
theorem bounded_frame_PQ_error {u h v k : ℝ → Space → ℂ}
    (A : ScalarCompactApproximation u h) (B : ScalarCompactApproximation v k) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n a b y z s r, 0 < a → 0 < b →
      mixedNorm volume volume 5 5 (fun t x =>
        normProduct (seedFrame a y s (1/2) u) (seedFrame b z r (1/2) v) t x -
        normProduct (seedFrame a y s (1/2) (A.value n)) (seedFrame b z r (1/2) (B.value n)) t x) ≤ C*smoothingPrecision n ∧
      mixedNorm volume volume 5 (ENNReal.ofReal (15/8 : ℝ)) (fun t x =>
        normProduct (seedFrame a y s (1/2) u) (seedFrame b z r (3/2) k) t x -
        normProduct (seedFrame a y s (1/2) (A.value n)) (seedFrame b z r (3/2) (B.gradient n)) t x) ≤ C*smoothingPrecision n := by
  let W := mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) k
  let C : ℝ≥0∞ := A.bound+B.bound+W
  have hC : C ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top,ENNReal.coe_ne_top⟩,B.profile.gradient_W⟩
  refine ⟨C,hC,?_⟩
  intro n a b y z s r ha hb
  have hAu := A.profile.frame ha y s
  have hAv := (A.approximate_profile n).frame ha y s
  have hBu := B.profile.frame hb z r
  have hBv := (B.approximate_profile n).frame hb z r
  have hn : smoothingPrecision n ≠ ∞ := ENNReal.ofReal_ne_top
  have hdu : mixedNorm volume volume 10 10
      (fun t x => seedFrame a y s (1/2) u t x-seedFrame a y s (1/2) (A.value n) t x) ≤ smoothingPrecision n := by
    rw [seedFrame_S_error ha y s u A.profile.value_joint.aestronglyMeasurable _ (A.approximate_profile n).value_joint.aestronglyMeasurable]
    exact A.value_error n
  have hdv : mixedNorm volume volume 10 10
      (fun t x => seedFrame b z r (1/2) v t x-seedFrame b z r (1/2) (B.value n) t x) ≤ smoothingPrecision n := by
    rw [seedFrame_S_error hb z r v B.profile.value_joint.aestronglyMeasurable _ (B.approximate_profile n).value_joint.aestronglyMeasurable]
    exact B.value_error n
  have hdk : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ))
      (fun t x => seedFrame b z r (3/2) k t x-seedFrame b z r (3/2) (B.gradient n) t x) ≤ smoothingPrecision n := by
    rw [seedFrame_W_error hb z r k B.profile.gradient_joint.aestronglyMeasurable _ (B.approximate_profile n).gradient_joint.aestronglyMeasurable]
    exact B.gradient_error n
  have hUb : mixedNorm volume volume 10 10 (seedFrame a y s (1/2) (A.value n)) ≤ A.bound := by
    rw [seedFrame_S_invariant ha y s _ (A.approximate_profile n).value_joint.aestronglyMeasurable]
    exact A.approximate_S_bound n
  have hvb : mixedNorm volume volume 10 10 (seedFrame b z r (1/2) v) ≤ B.bound := by
    rw [seedFrame_S_invariant hb z r v B.profile.value_joint.aestronglyMeasurable]
    exact B.value_S_bound
  have hkw : mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) (seedFrame b z r (3/2) k) = W :=
    seedFrame_W_invariant hb z r k B.profile.gradient_joint.aestronglyMeasurable
  constructor
  · let := value_product_holder
    have he := normProduct_difference_mixed_le (p := 10) (q := 10) (r := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      _ _ _ _ hAu.value_joint.aestronglyMeasurable hAv.value_joint.aestronglyMeasurable
      hBu.value_joint.aestronglyMeasurable hBv.value_joint.aestronglyMeasurable
      (ne_top_of_le_ne_top hn hdu) hBu.value_S hAv.value_S (ne_top_of_le_ne_top hn hdv)
    refine he.trans ((add_le_add (mul_le_mul' hdu hvb) (mul_le_mul' hUb hdv)).trans ?_)
    calc
      _ = ((A.bound : ℝ≥0∞)+B.bound)*smoothingPrecision n := by ring
      _ ≤ C*smoothingPrecision n := mul_le_mul' (le_add_right le_rfl) le_rfl
  · let := value_gradient_product_holder
    have he := normProduct_difference_mixed_le (p := 10) (q := ENNReal.ofReal (30/13 : ℝ))
      (r := ENNReal.ofReal (15/8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      _ _ _ _ hAu.value_joint.aestronglyMeasurable hAv.value_joint.aestronglyMeasurable
      hBu.gradient_joint.aestronglyMeasurable hBv.gradient_joint.aestronglyMeasurable
      (ne_top_of_le_ne_top hn hdu) hBu.gradient_W hAv.value_S (ne_top_of_le_ne_top hn hdk)
    rw [hkw] at he
    refine he.trans ((add_le_add (mul_le_mul' hdu le_rfl) (mul_le_mul' hUb hdk)).trans ?_)
    calc
      _ = ((A.bound : ℝ≥0∞)+W)*smoothingPrecision n := by ring
      _ ≤ C*smoothingPrecision n := mul_le_mul' (add_le_add (le_add_right le_rfl) le_rfl) le_rfl

#print axioms bounded_frame_PQ_error
end HartreeF.LocalProfileProducts
