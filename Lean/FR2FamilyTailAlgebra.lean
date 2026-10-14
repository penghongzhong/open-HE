import FR2ActualProfileFrames
import FR2ActualSquareTailBlocks
import FR2ActualTailForcing

/-! Finite actual nonlinear blocks and the exact augmented cancellation.
Only finite sums occur. All depth choices remain on the original retained
linear family. Author source, UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.R2FamilyTail
open EnergySpace SobolevStretch StationarySelfTest ProfileEnergy TimeHolder
  R2Global R2Frames R2SquareTail R2TailForcing

variable {ι : Type*} [DecidableEq ι]

theorem curveFinite_sum (s : Finset ι) (g : ι → ℝ → EnergyState)
    (hg : ∀ i ∈ s, CurveFinite (g i)) : CurveFinite (∑ i ∈ s, g i) := by
  revert hg
  induction s using Finset.induction_on with
  | empty => intro hg; simpa using CurveFinite.zero
  | @insert a s ha ih =>
      intro hg
      rw [Finset.sum_insert ha]
      exact (hg a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

theorem xNorm_sum_le (s : Finset ι) (g : ι → ℝ → EnergyState)
    (hg : ∀ i ∈ s, CurveFinite (g i)) :
    xNorm (∑ i ∈ s, g i) ≤ ∑ i ∈ s, xNorm (g i) := by
  revert hg
  induction s using Finset.induction_on with
  | empty => intro hg; simp only [Finset.sum_empty, xNorm_zero, le_refl]
  | @insert a s ha ih =>
      intro hg
      have hs := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (xNorm_add_le (hg a (Finset.mem_insert_self a s)) (curveFinite_sum s g hs)).trans
        (add_le_add le_rfl (ih hs))

def freeCurve (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (f : EnergyState) : ℝ → EnergyState := fun t => freeEnergyState hDensity hSob t f

def nonlinearFrame (P : LinearProfileFamily) (g : ℕ → ℝ → EnergyState)
    (j n : ℕ) : ℝ → EnergyState :=
  stateFrame (g j) (P.scale_pos j n) (P.center j n) (P.time j n)

def normalizedCorrection (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (g : ℕ → ℝ → EnergyState) (j : ℕ) : ℝ → EnergyState :=
  g j - freeCurve hDensity hSob (P.profile j)

def physicalCorrection (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (g : ℕ → ℝ → EnergyState) (j n : ℕ) : ℝ → EnergyState :=
  nonlinearFrame P g j n - freeCurve hDensity hSob (profileAtom hDensity hSob P j n)

def nonlinearBlock (P : LinearProfileFamily) (g : ℕ → ℝ → EnergyState)
    (L J n : ℕ) : ℝ → EnergyState := ∑ j ∈ Finset.Ico L J, nonlinearFrame P g j n

def augmentedCurve (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) (J n : ℕ) : ℝ → EnergyState :=
  (∑ j ∈ Finset.range J, nonlinearFrame P g j n) +
    freeCurve hDensity hSob (profileRemainder hDensity hSob P u J n)

theorem physicalCorrection_eq_frame (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (g : ℕ → ℝ → EnergyState) (j n : ℕ) :
    physicalCorrection hDensity hSob P g j n =
      stateFrame (normalizedCorrection hDensity hSob P g j)
        (P.scale_pos j n) (P.center j n) (P.time j n) := by
  symm
  exact stateFrame_correction hDensity hSob (g j) (P.profile j)
    (P.scale_pos j n) (P.center j n) (P.time j n)

theorem physicalCorrection_finite (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (g : ℕ → ℝ → EnergyState) (j n : ℕ)
    (h : CurveFinite (normalizedCorrection hDensity hSob P g j)) :
    CurveFinite (physicalCorrection hDensity hSob P g j n) := by
  rw [physicalCorrection_eq_frame]
  exact CurveFinite.stateFrame h (P.scale_pos j n) (P.center j n) (P.time j n)

theorem physicalCorrection_xNorm (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (g : ℕ → ℝ → EnergyState) (j n : ℕ)
    (h : Continuous (normalizedCorrection hDensity hSob P g j)) :
    xNorm (physicalCorrection hDensity hSob P g j n) =
      xNorm (normalizedCorrection hDensity hSob P g j) := by
  rw [physicalCorrection_eq_frame, stateFrame_xNorm h]

omit [DecidableEq ι] in
theorem freeCurve_sum (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (s : Finset ι) (f : ι → EnergyState) :
    freeCurve hDensity hSob (∑ i ∈ s, f i) = ∑ i ∈ s, freeCurve hDensity hSob (f i) := by
  funext t
  change (freeEnergyCLM hDensity hSob t) (∑ i ∈ s, f i) = _
  simp only [map_sum, Finset.sum_apply, freeCurve, freeEnergyCLM_apply]

/-- Exact finite algebra, before every spacetime norm or kinetic limit. -/
theorem nonlinearBlock_decomposition (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (g : ℕ → ℝ → EnergyState) (L J n : ℕ) :
    nonlinearBlock P g L J n =
      freeCurve hDensity hSob (actualLinearBlock hDensity hSob P L J n) +
        ∑ j ∈ Finset.Ico L J, physicalCorrection hDensity hSob P g j n := by
  rw [actualLinearBlock, freeCurve_sum]
  simp only [nonlinearBlock, physicalCorrection, Finset.sum_sub_distrib]
  abel

/-- Reconstruction cancels the full linear prefix at exactly the retained J. -/
theorem augmentedCurve_cancellation (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (g : ℕ → ℝ → EnergyState) (J n : ℕ) :
    augmentedCurve hDensity hSob P u g J n =
      freeCurve hDensity hSob (u n) +
        ∑ j ∈ Finset.range J, physicalCorrection hDensity hSob P g j n := by
  have he : freeCurve hDensity hSob (u n) =
      (∑ j ∈ Finset.range J, freeCurve hDensity hSob (profileAtom hDensity hSob P j n)) +
        freeCurve hDensity hSob (profileRemainder hDensity hSob P u J n) := by
    funext t
    change freeEnergyState hDensity hSob t (u n) = _
    conv_lhs => rw [profileRemainder_reconstruction hDensity hSob P u J n]
    change (freeEnergyCLM hDensity hSob t) (_ + _) = _
    simp only [map_add, map_sum, Pi.add_apply, Finset.sum_apply, freeCurve,
      freeEnergyCLM_apply]
  rw [he]
  simp only [augmentedCurve, physicalCorrection, Finset.sum_sub_distrib]
  abel

/-- A pure tail of actual corrections, uniformly for every original n. -/
theorem correction_block_bound (hDensity : OrdinaryH1Density) {K B m C : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hp : LinearProfileProperties hDensity hSob u P) (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (g : ℕ → ℝ → EnergyState) (hc : ∀ j, CurveFinite (normalizedCorrection hDensity hSob P g j))
    (hC : 0 ≤ C) (hm : 2 ≤ m) {L : ℕ}
    (hsmall : ∀ j ≥ L, xNorm (normalizedCorrection hDensity hSob P g j) ≤
      C * actualProfileSize P j ^ m) (J n : ℕ) :
    xNorm (∑ j ∈ Finset.Ico L J, physicalCorrection hDensity hSob P g j n) ≤
      C * actualProfileTail P L ^ m := by
  calc
    _ ≤ ∑ j ∈ Finset.Ico L J, xNorm (physicalCorrection hDensity hSob P g j n) :=
      xNorm_sum_le _ _ (fun j _ => physicalCorrection_finite hDensity hSob P g j n (hc j))
    _ = ∑ j ∈ Finset.Ico L J, xNorm (normalizedCorrection hDensity hSob P g j) :=
      Finset.sum_congr rfl (fun j _ => physicalCorrection_xNorm hDensity hSob P g j n
        (hc j).continuous)
    _ ≤ ∑ j ∈ Finset.Ico L J, C * actualProfileSize P j ^ m :=
      Finset.sum_le_sum (fun j hj => hsmall j (Finset.mem_Ico.mp hj).1)
    _ = C * ∑ j ∈ Finset.Ico L J, actualProfileSize P j ^ m := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (actualProfilePower_block_le_tail_rpow hDensity hSob P u hp hB hm L J) hC

/-- The N threshold depends on fixed L and J, whereas the numerical tail bound
has no J. The free estimate is consumed at the actual kinetic block. -/
theorem nonlinear_block_eventual_bound (hDensity : OrdinaryH1Density)
    {K B m C Cf : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (g : ℕ → ℝ → EnergyState)
    (hc : ∀ j, CurveFinite (normalizedCorrection hDensity hSob P g j))
    (hC : 0 ≤ C) (hCf : 0 ≤ Cf) (hm : 2 ≤ m)
    (hfree : ∀ f, CurveFinite (freeCurve hDensity hSob f) ∧
      xNorm (freeCurve hDensity hSob f) ≤ Cf*pureGradientNorm f)
    {L J : ℕ} (hLJ : L ≤ J) (hJ : (J : WithTop ℕ) ≤ P.count)
    (hsmall : ∀ j ≥ L, xNorm (normalizedCorrection hDensity hSob P g j) ≤
      C*actualProfileSize P j^m) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      CurveFinite (nonlinearBlock P g L J n) ∧
      xNorm (nonlinearBlock P g L J n) ≤
        Cf*(actualProfileTail P L+η)+C*actualProfileTail P L^m := by
  obtain ⟨N, hN⟩ := actualLinearBlock_eventually_le_tail_add hDensity hSob P u hp hB hLJ hJ hη
  refine ⟨N, fun n hn => ?_⟩
  rw [nonlinearBlock_decomposition hDensity hSob]
  have hf := hfree (actualLinearBlock hDensity hSob P L J n)
  have hz := curveFinite_sum (Finset.Ico L J) _
    (fun j _ => physicalCorrection_finite hDensity hSob P g j n (hc j))
  exact ⟨hf.1.add hz, (xNorm_add_le hf.1 hz).trans (add_le_add
    (hf.2.trans (mul_le_mul_of_nonneg_left (hN n hn) hCf))
    (correction_block_bound hDensity hSob P u hp hB g hc hC hm hsmall J n))⟩

private theorem prefix_le_head_add_tail (d : ℕ → ℝ) (hd : ∀ j, 0 ≤ d j)
    (L J : ℕ) :
    (∑ j ∈ Finset.range J, d j) ≤
      (∑ j ∈ Finset.range L, d j) + ∑ j ∈ Finset.Ico L J, d j := by
  by_cases hLJ : L ≤ J
  · exact (Finset.sum_range_add_sum_Ico d hLJ).ge
  · have hJL : J ≤ L := (Nat.lt_of_not_ge hLJ).le
    have he : Finset.Ico L J = ∅ := Finset.Ico_eq_empty_of_le hJL
    rw [he, Finset.sum_empty, add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hJL)
      (fun j _ _ => hd j)

/-- An all-index, all-depth correction cap. The finite head has a true finite
X norm; the tail is controlled by powers of the actual square tail. -/
theorem correction_prefix_bound (hDensity : OrdinaryH1Density) {K B m C : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (hp : LinearProfileProperties hDensity hSob u P) (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (g : ℕ → ℝ → EnergyState) (hc : ∀ j, CurveFinite (normalizedCorrection hDensity hSob P g j))
    (hC : 0 ≤ C) (hm : 2 ≤ m) (L : ℕ)
    (hsmall : ∀ j ≥ L, xNorm (normalizedCorrection hDensity hSob P g j) ≤
      C*actualProfileSize P j^m) (J n : ℕ) :
    xNorm (∑ j ∈ Finset.range J, physicalCorrection hDensity hSob P g j n) ≤
      (∑ j ∈ Finset.range L, xNorm (normalizedCorrection hDensity hSob P g j)) +
        C*actualProfileTail P L^m := by
  have htail : (∑ j ∈ Finset.Ico L J,
      xNorm (normalizedCorrection hDensity hSob P g j)) ≤ C*actualProfileTail P L^m := by
    calc
      _ ≤ ∑ j ∈ Finset.Ico L J, C*actualProfileSize P j^m :=
        Finset.sum_le_sum (fun j hj => hsmall j (Finset.mem_Ico.mp hj).1)
      _ = C*(∑ j ∈ Finset.Ico L J, actualProfileSize P j^m) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (actualProfilePower_block_le_tail_rpow hDensity hSob P u hp hB hm L J) hC
  calc
    _ ≤ ∑ j ∈ Finset.range J, xNorm (physicalCorrection hDensity hSob P g j n) :=
      xNorm_sum_le _ _ (fun j _ => physicalCorrection_finite hDensity hSob P g j n (hc j))
    _ = ∑ j ∈ Finset.range J, xNorm (normalizedCorrection hDensity hSob P g j) :=
      Finset.sum_congr rfl (fun j _ => physicalCorrection_xNorm hDensity hSob P g j n
        (hc j).continuous)
    _ ≤ _ := (prefix_le_head_add_tail _ (fun j => xNorm_nonneg _) L J).trans
      (add_le_add le_rfl htail)

/-- M is fixed before J, n, and every later residual tolerance. This uses the
literal cancellation, not a sum of all profile sizes or a growing B_J. -/
theorem exists_augmented_uniform_cap (hDensity : OrdinaryH1Density)
    {K B m C Cf : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (g : ℕ → ℝ → EnergyState)
    (hc : ∀ j, CurveFinite (normalizedCorrection hDensity hSob P g j))
    (hC : 0 ≤ C) (hCf : 0 ≤ Cf) (hm : 2 ≤ m)
    (hfree : ∀ f, CurveFinite (freeCurve hDensity hSob f) ∧
      xNorm (freeCurve hDensity hSob f) ≤ Cf*pureGradientNorm f)
    (L : ℕ) (hsmall : ∀ j ≥ L,
      xNorm (normalizedCorrection hDensity hSob P g j) ≤ C*actualProfileSize P j^m) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ J n,
      CurveFinite (augmentedCurve hDensity hSob P u g J n) ∧
      xNorm (augmentedCurve hDensity hSob P u g J n) ≤ M := by
  let H := ∑ j ∈ Finset.range L, xNorm (normalizedCorrection hDensity hSob P g j)
  let M := max 1 (Cf*B+H+C*actualProfileTail P L^m)
  refine ⟨M, le_max_left _ _, fun J n => ?_⟩
  rw [augmentedCurve_cancellation hDensity hSob]
  have hf := hfree (u n)
  have hz := curveFinite_sum (Finset.range J) _
    (fun j _ => physicalCorrection_finite hDensity hSob P g j n (hc j))
  refine ⟨hf.1.add hz, ?_⟩
  apply (xNorm_add_le hf.1 hz).trans
  have hb := add_le_add (hf.2.trans (mul_le_mul_of_nonneg_left (hB n) hCf))
    (correction_prefix_bound hDensity hSob P u hp hB g hc hC hm L hsmall J n)
  exact hb.trans ((le_of_eq (by dsimp [H]; ring)).trans (le_max_right _ _))

end HartreeF.R2FamilyTail
