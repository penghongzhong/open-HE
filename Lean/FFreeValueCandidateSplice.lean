import FFreeValueFullCandidate
import FCrossContinuityBounded
import FGeneralNestedNormTransport

/-! Same-direction free-value splice. Author source, UNCOMPILED.
The value argument remains nonlinear. Signed Riesz integral linearity is used
only after its genuine absolute fibre domains have been produced. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.FreeValueSplice
open TimeHolder ProfileApproximation GeneralProfileCross LocalProfileProducts
open ForcingDomain WeakHartreeChain DerivativeMajorization CompactCross CrossContinuity
open FreeValueFullCandidate

abbrev E (u : ℝ → Space → ℂ) : ℝ≥0∞ := mixedNorm volume volume ∞ 6 u
abbrev S (u : ℝ → Space → ℂ) : ℝ≥0∞ := mixedNorm volume volume 10 10 u
abbrev W (h : ℝ → Space → ℂ) : ℝ≥0∞ :=
  mixedNorm volume volume 10 (ENNReal.ofReal (30/13 : ℝ)) h

/-- The pre-existing directional candidate, with a time parameter. -/
def C (α c : ℝ) (u h : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t => directionalCandidate α c (u t) (h t)

/-- This is the derivative candidate of F(A+z)-F(A), never F(z). -/
def scalarDefect (α c : ℝ) (A z G h : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  C α c (A+z) (G+h) - C α c A G

def coordinateBound (α : ℝ) (Ccont KQ M d : ℝ≥0)
    (A h : ℝ → Space → ℂ) : ℝ≥0∞ :=
  2 * (Ccont : ℝ≥0∞) * boundedModulus α M d +
    (KQ : ℝ≥0∞) * E A ^ (2*α) * S A ^ (3 : ℝ) * Q A h

/-- A domain packet may change its direction without asserting a new weak
relation. In particular ScalarProfile A (G+h) does not assert G+h = grad A. -/
theorem scalarProfile_retarget {u v h k : ℝ → Space → ℂ}
    (hu : ScalarProfile u h) (hv : ScalarProfile v k) : ScalarProfile u k :=
  ⟨hu.value_joint, hv.gradient_joint, hu.value_V, hu.value_S, hv.gradient_W⟩

theorem scalarProfile_add {u v h k : ℝ → Space → ℂ}
    (hu : ScalarProfile u h) (hv : ScalarProfile v k) : ScalarProfile (u+v) (h+k) := by
  refine ⟨hu.value_joint.add hv.value_joint, hu.gradient_joint.add hv.gradient_joint, ?_, ?_, ?_⟩
  · exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hu.value_V, hv.value_V⟩)
      (mixed_add_le (by simp) (by norm_num) (by norm_num) u v
        hu.value_joint.aestronglyMeasurable hv.value_joint.aestronglyMeasurable)
  · exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hu.value_S, hv.value_S⟩)
      (mixed_add_le (by norm_num) (by norm_num) (by norm_num) u v
        hu.value_joint.aestronglyMeasurable hv.value_joint.aestronglyMeasurable)
  · exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hu.gradient_W, hv.gradient_W⟩)
      (mixed_add_le (by norm_num) (by norm_num) (by norm_num) h k
        hu.gradient_joint.aestronglyMeasurable hv.gradient_joint.aestronglyMeasurable)

theorem scalarProfile_Q_finite {u h : ℝ → Space → ℂ} (hu : ScalarProfile u h) :
    Q u h ≠ ∞ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hu.value_S hu.gradient_W)
    (Q_le u h hu.value_joint.aestronglyMeasurable hu.gradient_joint.aestronglyMeasurable
      hu.value_S hu.gradient_W)

/-- Both signed fibres are retained before invoking integral_add. -/
theorem directionalCandidate_add (α c : ℝ) (u G h : Space → ℂ) (x : Space)
    (hG : Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α u G y) volume)
    (hh : Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α u h y) volume) :
    directionalCandidate α c u (G+h) x =
      directionalCandidate α c u G x + directionalCandidate α c u h x := by
  have hd : rieszConvolution α c (directionalDensity α u (G+h)) x =
      rieszConvolution α c (directionalDensity α u G) x +
        rieszConvolution α c (directionalDensity α u h) x := by
    unfold rieszConvolution
    simp only [directionalDensity, Pi.add_apply, map_add, mul_add]
    exact integral_add hG hh
  simp only [directionalCandidate, hd, Pi.add_apply, map_add, add_smul, smul_add]
  abel

/-- Signed subtraction uses the same two absolute fibre domains. -/
theorem directionalCandidate_sub (α c : ℝ) (u G h : Space → ℂ) (x : Space)
    (hG : Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α u G y) volume)
    (hh : Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α u h y) volume) :
    directionalCandidate α c u (G-h) x =
      directionalCandidate α c u G x - directionalCandidate α c u h x := by
  have hd : rieszConvolution α c (directionalDensity α u (G-h)) x =
      rieszConvolution α c (directionalDensity α u G) x -
        rieszConvolution α c (directionalDensity α u h) x := by
    unfold rieszConvolution
    simp only [directionalDensity, Pi.sub_apply, map_sub, mul_sub]
    exact integral_sub hG hh
  simp only [directionalCandidate, hd, Pi.sub_apply, map_sub, sub_smul, smul_sub]
  abel

/-- Real homogeneity on the same signed domain; it also supplies the scaled
absolute domain, including the scalar zero case. -/
theorem directionalCandidate_real_smul (α c r : ℝ) (u h : Space → ℂ) (x : Space)
    (hh : Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α u h y) volume) :
    Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α u (r • h) y) volume ∧
    directionalCandidate α c u (r • h) x = r • directionalCandidate α c u h x := by
  have heq : (fun y => rieszKernel α c (x-y) * directionalDensity α u (r • h) y) =
      (fun y => r * (rieszKernel α c (x-y) * directionalDensity α u h y)) := by
    funext y
    simp only [directionalDensity, Pi.smul_apply, map_smul, smul_eq_mul]
    ring
  refine ⟨by rw [heq]; exact hh.const_mul r, ?_⟩
  have hd : rieszConvolution α c (directionalDensity α u (r • h)) x =
      r * rieszConvolution α c (directionalDensity α u h) x := by
    unfold rieszConvolution
    rw [heq, integral_const_mul]
  simp only [directionalCandidate, hd, Pi.smul_apply, map_smul, smul_add,
    mul_smul, smul_comm]

/-- This is literal algebra in the value difference. The only distributed
integral is the signed directional fibre with the fixed value A. -/
theorem literal_splice (α c : ℝ) (A z G h : Space → ℂ) (x : Space)
    (hG : Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α A G y) volume)
    (hh : Integrable (fun y => rieszKernel α c (x-y) * directionalDensity α A h y) volume) :
    directionalCandidate α c (A+z) (G+h) x - directionalCandidate α c A G x =
      (directionalCandidate α c (A+z) (G+h) x - directionalCandidate α c A (G+h) x) +
        directionalCandidate α c A h x := by
  rw [directionalCandidate_add α c A G h x hG hh]
  abel

/-- A concrete finite-profile packet produces full signed candidate control.
There is no input hypothesis about the target candidate or its norm. -/
theorem scalarProfile_full_control {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ KQ : ℝ≥0, ∀ (u h : ℝ → Space → ℂ), ScalarProfile u h →
      FullCandidateControl α c u h KQ := by
  obtain ⟨KQ, hK⟩ := full_candidate_bound hH
  exact ⟨KQ, fun u h hu => hK u h hu.value_joint hu.gradient_joint
    hu.value_V hu.value_S (scalarProfile_Q_finite hu)⟩

/-- Every-index finiteness uses the actual E/S/W domains, independently of the
single bounded-set cap that will be fixed before the selected depth. -/
theorem scalar_defect_finite {α c : ℝ} (hH : OrdinaryHLS α c)
    {A z G h : ℝ → Space → ℂ} (hA : ScalarProfile A G) (hz : ScalarProfile z h) :
    AEStronglyMeasurable (fun p : ℝ × Space => scalarDefect α c A z G h p.1 p.2)
      (volume.prod volume) ∧ forcingNorm (scalarDefect α c A z G h) ≠ ∞ := by
  obtain ⟨KQ, hK⟩ := scalarProfile_full_control hH
  have hsum := hK (A+z) (G+h) (scalarProfile_add hA hz)
  have hbase := hK A G hA
  have hm := hsum.candidate_joint.sub hbase.candidate_joint
  refine ⟨hm, ?_⟩
  have ht : forcingNorm (scalarDefect α c A z G h) ≤
      forcingNorm (C α c (A+z) (G+h)) + forcingNorm (C α c A G) := by
    apply mixed_norm_le_add_of_domination volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) _ _ _ hm
      hsum.candidate_joint hbase.candidate_joint
    filter_upwards [] with t
    filter_upwards [] with x
    exact norm_sub_le _ _
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hsum.candidate_finite, hbase.candidate_finite⟩) ht

/-- The enlarged value size is controlled using only the two original values. -/
theorem same_valueSize_le {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hqt : q ≠ ∞)
    (A z : ℝ → Space → ℂ)
    (hA : AEStronglyMeasurable (fun p : ℝ × Space => A p.1 p.2) (volume.prod volume))
    (hz : AEStronglyMeasurable (fun p : ℝ × Space => z p.1 p.2) (volume.prod volume)) :
    valueSize p q (A+z) A (A+z) A ≤
      4 * mixedNorm volume volume p q A + 2 * mixedNorm volume volume p q z := by
  have ht := mixed_add_le hp hq hqt A z hA hz
  unfold valueSize
  calc
    _ ≤ ((mixedNorm volume volume p q A + mixedNorm volume volume p q z) +
          mixedNorm volume volume p q A) +
        ((mixedNorm volume volume p q A + mixedNorm volume volume p q z) +
          mixedNorm volume volume p q A) := add_le_add (add_le_add_right ht _) (add_le_add_right ht _)
    _ = _ := by ring

@[simp] theorem same_changeSize (p q : ℝ≥0∞) (A z : ℝ → Space → ℂ) :
    changeSize p q (A+z) A (A+z) A = 2 * mixedNorm volume volume p q z := by
  simp only [changeSize, add_sub_cancel_left, two_mul]

@[simp] theorem identical_changeSize (p q : ℝ≥0∞) (T : ℝ → Space → ℂ) :
    changeSize p q T T T T = 0 := by
  simp [changeSize, mixedNorm]

/-- Fixed-value-direction continuity: both derivative placements use T=G+h.
No small directional W norm is used. Both M and d are genuinely finite NNReal. -/
theorem same_direction_continuity {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ Ccont : ℝ≥0, ∀ (A z G h : ℝ → Space → ℂ),
      ScalarProfile A G → ScalarProfile z h → ∀ (M d : ℝ≥0),
      4*E A + 2*E z ≤ M → 4*S A + 2*S z ≤ M → 2*W (G+h) ≤ M → 2*S z ≤ d →
      forcingNorm (C α c (A+z) (G+h) - C α c A (G+h)) ≤
        2 * (Ccont : ℝ≥0∞) * boundedModulus α M d := by
  obtain ⟨Ccont, hC⟩ := separate_cross_bounded_continuity hH
  refine ⟨Ccont, ?_⟩
  intro A z G h hA hz M d hE hS hW hd
  have hsum := scalarProfile_add hA hz
  have hAT := scalarProfile_retarget hA hsum
  have hJ := hsum.jointInputs hAT hsum hAT
  have hs := hsum.sliceInputs hAT hsum hAT
  have hE' := (same_valueSize_le (p := ∞) (q := 6) (by simp) (by norm_num) (by norm_num)
    A z hA.value_joint.aestronglyMeasurable hz.value_joint.aestronglyMeasurable).trans hE
  have hS' := (same_valueSize_le (p := 10) (q := 10) (by norm_num) (by norm_num) (by norm_num)
    A z hA.value_joint.aestronglyMeasurable hz.value_joint.aestronglyMeasurable).trans hS
  have hW' : referenceSize (G+h) (G+h) ≤ M := by simpa only [referenceSize, two_mul] using hW
  have hd' : changeSize 10 10 (A+z) A (A+z) A ≤ d := by simpa only [same_changeSize] using hd
  have hdir : changeSize 10 (ENNReal.ofReal (30/13 : ℝ)) (G+h) (G+h) (G+h) (G+h) ≤ d := by
    rw [identical_changeSize]
    exact bot_le
  obtain ⟨_, _, hi, ho⟩ := hC (A+z) A (G+h) (G+h) (A+z) A (G+h) (G+h)
    hJ hs M d hE' hS' hW' hd' hdir
  have hmi := (inner_joint_measurable α c hsum.value_joint.aestronglyMeasurable
    hsum.gradient_joint.aestronglyMeasurable hsum.value_joint.aestronglyMeasurable).sub
      (inner_joint_measurable α c hA.value_joint.aestronglyMeasurable
        hsum.gradient_joint.aestronglyMeasurable hA.value_joint.aestronglyMeasurable)
  have hmo := (outer_joint_measurable α c hsum.value_joint.aestronglyMeasurable
    hsum.value_joint.aestronglyMeasurable hsum.gradient_joint.aestronglyMeasurable).sub
      (outer_joint_measurable α c hA.value_joint.aestronglyMeasurable
        hA.value_joint.aestronglyMeasurable hsum.gradient_joint.aestronglyMeasurable)
  have heq : C α c (A+z) (G+h) - C α c A (G+h) =
      (innerCross α c (A+z) (G+h) (A+z) - innerCross α c A (G+h) A) +
      (outerCross α c (A+z) (A+z) (G+h) - outerCross α c A A (G+h)) := by
    funext t x
    dsimp [C, directionalCandidate, innerCross, outerCross]
    abel
  rw [heq]
  calc
    _ ≤ forcingNorm (innerCross α c (A+z) (G+h) (A+z) - innerCross α c A (G+h) A) +
        forcingNorm (outerCross α c (A+z) (A+z) (G+h) - outerCross α c A A (G+h)) :=
      mixed_add_le (by norm_num) (by norm_num) (by norm_num) _ _ hmi hmo
    _ ≤ (Ccont : ℝ≥0∞)*boundedModulus α M d + (Ccont : ℝ≥0∞)*boundedModulus α M d := add_le_add hi ho
    _ = _ := by ring

/-- All four packets are retained: they are genuine source domains, not invented
weak-gradient relations for the mixed pair (A,G+h). -/
structure SpliceControl (α c : ℝ) (A z G h : ℝ → Space → ℂ)
    (Ccont KQ M d : ℝ≥0) : Prop where
  sum_profile : ScalarProfile (A+z) (G+h)
  fixed_profile : ScalarProfile A (G+h)
  base_profile : ScalarProfile A G
  free_direction_profile : ScalarProfile A h
  sum_control : FullCandidateControl α c (A+z) (G+h) KQ
  fixed_control : FullCandidateControl α c A (G+h) KQ
  base_control : FullCandidateControl α c A G KQ
  free_direction_control : FullCandidateControl α c A h KQ
  splice : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
    scalarDefect α c A z G h t x =
      (C α c (A+z) (G+h) t x - C α c A (G+h) t x) + C α c A h t x
  scalarDefect_joint : AEStronglyMeasurable
    (fun p : ℝ × Space => scalarDefect α c A z G h p.1 p.2) (volume.prod volume)
  scalarDefect_finite : forcingNorm (scalarDefect α c A z G h) ≠ ∞
  bound : forcingNorm (scalarDefect α c A z G h) ≤ coordinateBound α Ccont KQ M d A h

/-- Constants are selected before the fields, frame, extraction depth or index. -/
theorem same_direction_free_value_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ Ccont KQ : ℝ≥0, ∀ (A z G h : ℝ → Space → ℂ),
      ScalarProfile A G → ScalarProfile z h → ∀ (M d : ℝ≥0),
      4*E A + 2*E z ≤ M → 4*S A + 2*S z ≤ M → 2*W (G+h) ≤ M → 2*S z ≤ d →
      SpliceControl α c A z G h Ccont KQ M d := by
  obtain ⟨Ccont, hC⟩ := same_direction_continuity hH
  obtain ⟨KQ, hK⟩ := scalarProfile_full_control hH
  refine ⟨Ccont, KQ, ?_⟩
  intro A z G h hA hz M d hE hS hW hd
  have hpSum := scalarProfile_add hA hz
  have hpFixed := scalarProfile_retarget hA hpSum
  have hpFree := scalarProfile_retarget hA hz
  have hcSum := hK (A+z) (G+h) hpSum
  have hcFixed := hK A (G+h) hpFixed
  have hcBase := hK A G hA
  have hcFree := hK A h hpFree
  have hsplice : ∀ᵐ t ∂volume, ∀ᵐ x ∂volume,
      scalarDefect α c A z G h t x =
        (C α c (A+z) (G+h) t x - C α c A (G+h) t x) + C α c A h t x := by
    filter_upwards [hcBase.directional_fibres, hcFree.directional_fibres] with t htG hth
    filter_upwards [htG, hth] with x hxG hxh
    exact literal_splice α c (A t) (z t) (G t) (h t) x hxG hxh
  obtain ⟨hm, hf⟩ := scalar_defect_finite hH hA hz
  refine ⟨hpSum, hpFixed, hA, hpFree, hcSum, hcFixed, hcBase, hcFree, hsplice, hm, hf, ?_⟩
  have heq := mixedNorm_congr_nested_ae volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) hsplice
  change forcingNorm (scalarDefect α c A z G h) =
    forcingNorm ((C α c (A+z) (G+h) - C α c A (G+h)) + C α c A h) at heq
  rw [heq]
  exact (mixed_add_le (by norm_num) (by norm_num) (by norm_num) _ _
    (hcSum.candidate_joint.sub hcFixed.candidate_joint) hcFree.candidate_joint).trans
      (add_le_add (hC A z G h hA hz M d hE hS hW hd) hcFree.candidate_bound)

#print axioms directionalCandidate_add
#print axioms directionalCandidate_sub
#print axioms directionalCandidate_real_smul
#print axioms literal_splice
#print axioms scalar_defect_finite
#print axioms same_direction_continuity
#print axioms same_direction_free_value_bound
end HartreeF.FreeValueSplice
