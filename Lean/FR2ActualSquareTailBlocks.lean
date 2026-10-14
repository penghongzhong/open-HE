import FOrdinaryLinearProfileInterface
import FR2SquareTailPowers
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Actual square tails and fixed-depth kinetic blocks on the original retained
sequence. This file is source-only: no native verification is claimed.

Square summability is produced from the existing eligible kinetic identities,
the original uniform pure-gradient bound, and literal inactive-zero padding.
The finite-block weak limit uses only hp.weak_remainder at its fixed eligible
upper depth. No pairwise orthogonality or common-in-depth threshold is assumed.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.R2SquareTail
open EnergySpace SobolevStretch StationarySelfTest ProfileEnergy
attribute [local irreducible] energySubmodule

/-- The actual original profile's pure-gradient size. -/
def actualProfileSize (P : LinearProfileFamily) (j : ℕ) : ℝ :=
  pureGradientNorm (P.profile j)

theorem actualProfileSize_nonneg (P : LinearProfileFamily) (j : ℕ) :
    0 ≤ actualProfileSize P j := pureGradientNorm_nonneg _

/-- Every eligible kinetic prefix is bounded by the original sequence cap.
Neither the input kinetic energies nor the remainder energies must converge. -/
theorem actualProfileSquare_prefix_le_of_eligible (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J : ℕ)
    (hJ : (J : WithTop ℕ) ≤ P.count) :
    ∑ j ∈ Finset.range J, actualProfileSize P j ^ 2 ≤ B ^ 2 := by
  have hB0 : 0 ≤ B := (pureGradientNorm_nonneg (u 0)).trans (hB 0)
  have hu (n : ℕ) : gradientSquared (u n) ≤ B ^ 2 := by
    rw [← pureGradientNorm_sq]
    exact (sq_le_sq₀ (pureGradientNorm_nonneg (u n)) hB0).mpr (hB n)
  have hk : 0 ≤ B ^ 2 - ∑ j ∈ Finset.range J, gradientSquared (P.profile j) := by
    apply le_of_tendsto (hp.kinetic J hJ)
    exact Filter.Eventually.of_forall (fun n => by
      have hr := gradientSquared_nonneg (profileRemainder hDensity hSob P u J n)
      linarith [hu n])
  simpa only [actualProfileSize, pureGradientNorm_sq] using (sub_nonneg.mp hk)

/-- The square sum itself, not just the remainder, has literal finite padding. -/
theorem actualProfileSquare_finite_padding (P : LinearProfileFamily) (N J : ℕ)
    (hcount : P.count = (N : WithTop ℕ)) (hNJ : N ≤ J) :
    (∑ j ∈ Finset.range J, actualProfileSize P j ^ 2) =
      ∑ j ∈ Finset.range N, actualProfileSize P j ^ 2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNJ
  clear hNJ
  induction d with
  | zero => simp
  | succ d hd =>
    have hi : ¬((N + d : ℕ) : WithTop ℕ) < P.count := by
      rw [hcount]
      exact not_lt.mpr (by exact_mod_cast Nat.le_add_right N d)
    rw [Nat.add_succ, Finset.sum_range_succ, hd]
    simp only [actualProfileSize, P.inactive_zero (N + d) hi,
      pureGradientNorm, gradientSquared, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, Real.sqrt_zero, add_zero]

/-- All finite prefixes are bounded, including prefixes past a finite count. -/
theorem actualProfileSquare_prefix_le (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (J : ℕ) :
    ∑ j ∈ Finset.range J, actualProfileSize P j ^ 2 ≤ B ^ 2 := by
  cases hcount : P.count with
  | top =>
    exact actualProfileSquare_prefix_le_of_eligible hDensity hSob P u hp hB J
      (by simp [hcount])
  | coe N =>
    have hc : P.count = (N : WithTop ℕ) := hcount
    by_cases hJN : J ≤ N
    · exact actualProfileSquare_prefix_le_of_eligible hDensity hSob P u hp hB J
        (by rw [hc]; exact_mod_cast hJN)
    · have hNJ : N ≤ J := (Nat.lt_of_not_ge hJN).le
      rw [actualProfileSquare_finite_padding P N J hc hNJ]
      exact actualProfileSquare_prefix_le_of_eligible hDensity hSob P u hp hB N
        (by simp [hc])

/-- Genuine square summability, independently produced before taking tails. -/
theorem actualProfileSquare_summable (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) :
    Summable (fun j : ℕ => actualProfileSize P j ^ 2) :=
  summable_of_sum_range_le (fun j => sq_nonneg (actualProfileSize P j))
    (actualProfileSquare_prefix_le hDensity hSob P u hp hB)

theorem actualProfileSquare_tsum_le (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) :
    (∑' j : ℕ, actualProfileSize P j ^ 2) ≤ B ^ 2 :=
  Real.tsum_le_of_sum_range_le (fun j => sq_nonneg (actualProfileSize P j))
    (actualProfileSquare_prefix_le hDensity hSob P u hp hB)

/-- The true square tail, indexed in the source order L+k. -/
def actualProfileTail (P : LinearProfileFamily) (L : ℕ) : ℝ :=
  squareTail (actualProfileSize P) L

theorem actualProfileTail_nonneg (P : LinearProfileFamily) (L : ℕ) :
    0 ≤ actualProfileTail P L := squareTail_nonneg _ _

theorem actualProfileTail_sq (P : LinearProfileFamily) (L : ℕ) :
    actualProfileTail P L ^ 2 = ∑' k : ℕ, actualProfileSize P (L + k) ^ 2 :=
  squareTail_sq _ _

/-- This tail limit consumes the actual summability proof above. -/
theorem actualProfileTail_tendsto_zero (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) :
    Tendsto (actualProfileTail P) atTop (𝓝 0) :=
  squareTail_tendsto_zero (actualProfileSquare_summable hDensity hSob P u hp hB)

/-- Every actual profile in a tail is dominated by its square-tail norm. -/
theorem actualProfileSize_le_tail (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) {L j : ℕ} (hLj : L ≤ j) :
    actualProfileSize P j ≤ actualProfileTail P L :=
  le_squareTail (actualProfileSize_nonneg P)
    (actualProfileSquare_summable hDensity hSob P u hp hB) hLj

/-- The actual countable family has no nonsmall labels arbitrarily far out. -/
theorem actualProfileSize_tendsto_zero (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) :
    Tendsto (actualProfileSize P) atTop (𝓝 0) := by
  exact squeeze_zero (actualProfileSize_nonneg P)
    (fun j => actualProfileSize_le_tail hDensity hSob P u hp hB (le_refl j))
    (actualProfileTail_tendsto_zero hDensity hSob P u hp hB)

theorem actualProfileSize_eventually_le (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L₀ : ℕ, ∀ j ≥ L₀, actualProfileSize P j ≤ δ := by
  have he := (actualProfileSize_tendsto_zero hDensity hSob P u hp hB).eventually
    (eventually_lt_nhds hδ)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp he
  exact ⟨L₀, fun j hj => (hL₀ j hj).le⟩

/-- Only finitely many actual labels exceed any fixed positive size. -/
theorem actualProfileSize_nonsmall_finite (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) {δ : ℝ} (hδ : 0 < δ) :
    Set.Finite {j : ℕ | δ < actualProfileSize P j} := by
  obtain ⟨L₀, hL₀⟩ := actualProfileSize_eventually_le hDensity hSob P u hp hB hδ
  apply (Set.finite_Iio L₀).subset
  intro j hj
  change j < L₀
  by_contra hjL
  exact (not_lt_of_ge (hL₀ j (le_of_not_gt hjL))) hj

/-- The literal finite source-order block, without a new linear family. -/
def actualLinearBlock (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (L J n : ℕ) : EnergyState :=
  ∑ j ∈ Finset.Ico L J, profileAtom hDensity hSob P j n

theorem actualLinearBlock_self (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (L n : ℕ) :
    actualLinearBlock hDensity hSob P L L n = 0 := by
  simp [actualLinearBlock]

/-- Exact finite reconstruction fixes the subtraction order rL-rJ. -/
theorem actualLinearBlock_eq_remainder_sub (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    {L J : ℕ} (hLJ : L ≤ J) (n : ℕ) :
    actualLinearBlock hDensity hSob P L J n =
      profileRemainder hDensity hSob P u L n - profileRemainder hDensity hSob P u J n := by
  unfold actualLinearBlock
  rw [Finset.sum_Ico_eq_sub _ hLJ]
  simp only [profileRemainder]
  abel

/-- Real coordinate-gradient pairing commutes with a finite actual state sum. -/
theorem gradientPair_finset_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → EnergyState) (v : EnergyState) :
    gradientPair (∑ j ∈ s, f j) v = ∑ j ∈ s, gradientPair (f j) v := by
  simp only [gradientPair, map_sum, sum_inner]
  exact Finset.sum_comm

theorem gradientPair_comm (u v : EnergyState) : gradientPair u v = gradientPair v u := by
  exact Finset.sum_congr rfl (fun j _ => real_inner_comm _ _)

/-- An individual source-order frame is paired with the genuine inverse-frame
weak remainder, using the frame's real-gradient isometry. -/
theorem actualProfileAtom_remainder_pair_tendsto (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    {J j : ℕ} (hj : j < J) (hJ : (J : WithTop ℕ) ≤ P.count) :
    Tendsto (fun n => gradientPair (profileAtom hDensity hSob P j n)
      (profileRemainder hDensity hSob P u J n)) atTop (𝓝 0) := by
  let A (n : ℕ) := linearProfileFrame hDensity hSob
    (P.scale j n) (P.scale_pos j n) (P.center j n) (P.time j n)
  have hw := hp.weak_remainder J j hj hJ
  have ht : Tendsto (fun n => gradientPair
      ((A n).symm (profileRemainder hDensity hSob P u J n)) (P.profile j))
      atTop (𝓝 0) := by
    simpa only [gradientPair, map_zero, inner_zero_left, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun k _ => hw k (energyGradient k (P.profile j)))
  have he (n : ℕ) : gradientPair (profileAtom hDensity hSob P j n)
      (profileRemainder hDensity hSob P u J n) =
      gradientPair ((A n).symm (profileRemainder hDensity hSob P u J n)) (P.profile j) := by
    have hh := linearProfileFrame_gradientPair hDensity hSob
      (P.scale j n) (P.scale_pos j n) (P.center j n) (P.time j n)
      ((A n).symm (profileRemainder hDensity hSob P u J n)) (P.profile j)
    change gradientPair (A n ((A n).symm (profileRemainder hDensity hSob P u J n)))
      (A n (P.profile j)) = _ at hh
    rw [ContinuousLinearEquiv.apply_symm_apply] at hh
    change gradientPair (A n (P.profile j)) (profileRemainder hDensity hSob P u J n) = _
    rw [gradientPair_comm]
    exact hh
  simpa only [he] using ht

/-- Finite summation is at one fixed eligible depth J. No inactive-label weak
condition, pairwise profile orthogonality, or depth-uniform limit is used. -/
theorem actualLinearBlock_remainder_pair_tendsto (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (L J : ℕ) (hJ : (J : WithTop ℕ) ≤ P.count) :
    Tendsto (fun n => gradientPair (actualLinearBlock hDensity hSob P L J n)
      (profileRemainder hDensity hSob P u J n)) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum (Finset.Ico L J) (fun j hj =>
    actualProfileAtom_remainder_pair_tendsto hDensity hSob P u hp
      (Finset.mem_Ico.mp hj).2 hJ)
  simpa only [actualLinearBlock, gradientPair_finset_sum_left, Finset.sum_const_zero] using ht

/-- Subtracting the two literal kinetic identities gives the fixed block limit
on the original retained sequence, without taking a further subsequence. -/
theorem actualLinearBlock_kinetic_tendsto (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    {L J : ℕ} (hLJ : L ≤ J) (hJ : (J : WithTop ℕ) ≤ P.count) :
    Tendsto (fun n => pureGradientNorm (actualLinearBlock hDensity hSob P L J n) ^ 2)
      atTop (𝓝 (∑ j ∈ Finset.Ico L J, actualProfileSize P j ^ 2)) := by
  have hL : (L : WithTop ℕ) ≤ P.count :=
    le_trans (by exact_mod_cast hLJ) hJ
  let κ (I n : ℕ) := gradientSquared (u n) -
    (∑ j ∈ Finset.range I, gradientSquared (P.profile j)) -
    gradientSquared (profileRemainder hDensity hSob P u I n)
  have hκJ : Tendsto (κ J) atTop (𝓝 0) := hp.kinetic J hJ
  have hκL : Tendsto (κ L) atTop (𝓝 0) := hp.kinetic L hL
  have hc := actualLinearBlock_remainder_pair_tendsto hDensity hSob P u hp L J hJ
  have hs : (∑ j ∈ Finset.range L, gradientSquared (P.profile j)) +
      (∑ j ∈ Finset.Ico L J, gradientSquared (P.profile j)) =
      ∑ j ∈ Finset.range J, gradientSquared (P.profile j) :=
    Finset.sum_range_add_sum_Ico (fun j => gradientSquared (P.profile j)) hLJ
  have he (n : ℕ) : gradientSquared (actualLinearBlock hDensity hSob P L J n) =
      (∑ j ∈ Finset.Ico L J, gradientSquared (P.profile j)) +
        ((κ J n - κ L n) - 2 * gradientPair (actualLinearBlock hDensity hSob P L J n)
          (profileRemainder hDensity hSob P u J n)) := by
    have hr : profileRemainder hDensity hSob P u L n =
        actualLinearBlock hDensity hSob P L J n + profileRemainder hDensity hSob P u J n := by
      rw [actualLinearBlock_eq_remainder_sub hDensity hSob P u hLJ n]
      abel
    have hpola := gradientSquared_add_pair (actualLinearBlock hDensity hSob P L J n)
      (profileRemainder hDensity hSob P u J n)
    rw [← hr] at hpola
    dsimp only [κ]
    linarith
  have ht : Tendsto (fun n => (∑ j ∈ Finset.Ico L J, gradientSquared (P.profile j)) +
      ((κ J n - κ L n) - 2 * gradientPair (actualLinearBlock hDensity hSob P L J n)
        (profileRemainder hDensity hSob P u J n))) atTop
      (𝓝 (∑ j ∈ Finset.Ico L J, gradientSquared (P.profile j))) := by
    simpa only [sub_self, mul_zero, sub_zero, add_zero] using
      (tendsto_const_nhds (x := ∑ j ∈ Finset.Ico L J, gradientSquared (P.profile j))).add
        ((hκJ.sub hκL).sub (hc.const_mul 2))
  simpa only [actualProfileSize, pureGradientNorm_sq, he] using ht

/-- Every finite square block is controlled by the genuine actual square tail. -/
theorem actualProfileSquare_block_le_tail_sq (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (L J : ℕ) :
    (∑ j ∈ Finset.Ico L J, actualProfileSize P j ^ 2) ≤ actualProfileTail P L ^ 2 :=
  sum_Ico_sq_le_squareTail_sq
    (actualProfileSquare_summable hDensity hSob P u hp hB) L J

/-- Actual finite higher-power tails are derived from the square sum, including
zero tails and empty blocks. No summability of the profile sizes is assumed. -/
theorem actualProfilePower_block_le_tail_rpow (hDensity : OrdinaryH1Density)
    {K B m : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (hm : 2 ≤ m) (L J : ℕ) :
    (∑ j ∈ Finset.Ico L J, actualProfileSize P j ^ m) ≤ actualProfileTail P L ^ m :=
  sum_Ico_rpow_le_squareTail_rpow (actualProfileSize_nonneg P)
    (actualProfileSquare_summable hDensity hSob P u hp hB) hm L J

/-- Genuine higher-power tail summability is established before its tsum bound. -/
theorem actualProfilePower_tail_summable (hDensity : OrdinaryH1Density)
    {K B m : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (hm : 2 ≤ m) (L : ℕ) :
    Summable (fun k : ℕ => actualProfileSize P (L + k) ^ m) :=
  summable_tail_rpow (actualProfileSize_nonneg P)
    (actualProfileSquare_summable hDensity hSob P u hp hB) hm L

theorem actualProfilePower_tsum_le_tail_rpow (hDensity : OrdinaryH1Density)
    {K B m : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) (hm : 2 ≤ m) (L : ℕ) :
    (∑' k : ℕ, actualProfileSize P (L + k) ^ m) ≤ actualProfileTail P L ^ m :=
  tsum_tail_rpow_le_squareTail_rpow (actualProfileSize_nonneg P)
    (actualProfileSquare_summable hDensity hSob P u hp hB) hm L

/-- The numerical bound is independent of J; the selected threshold is for this
fixed eligible L,J and eta. In particular this is not a uniform-in-J N. -/
theorem actualLinearBlock_eventually_le_tail_add (hDensity : OrdinaryH1Density)
    {K B : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hp : LinearProfileProperties hDensity hSob u P)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B) {L J : ℕ}
    (hLJ : L ≤ J) (hJ : (J : WithTop ℕ) ≤ P.count) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N,
      pureGradientNorm (actualLinearBlock hDensity hSob P L J n) ≤ actualProfileTail P L + η := by
  have he0 := actualProfileTail_nonneg P L
  have hs := actualProfileSquare_block_le_tail_sq hDensity hSob P u hp hB L J
  have hstrict : (∑ j ∈ Finset.Ico L J, actualProfileSize P j ^ 2) <
      (actualProfileTail P L + η) ^ 2 := by
    nlinarith [mul_nonneg he0 hη.le, sq_pos_of_pos hη]
  have he := (actualLinearBlock_kinetic_tendsto hDensity hSob P u hp hLJ hJ).eventually
    (eventually_lt_nhds hstrict)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun n hn => ?_⟩
  exact (sq_le_sq₀ (pureGradientNorm_nonneg _) (add_nonneg he0 hη.le)).mp (hN n hn).le

/-- The actual remainder at any finite depth reduces to the eligible finite
terminal depth before any kinetic or weak statement is consumed. -/
theorem profileRemainder_eq_min_finite (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    (N I n : ℕ) (hcount : P.count = (N : WithTop ℕ)) :
    profileRemainder hDensity hSob P u I n =
      profileRemainder hDensity hSob P u (min I N) n := by
  by_cases hIN : I ≤ N
  · rw [min_eq_left hIN]
  · have hNI : N ≤ I := (Nat.lt_of_not_ge hIN).le
    rw [min_eq_right hNI]
    exact profileRemainder_finite_padding hDensity hSob P u N I n hcount hNI

/-- Padding is an exact block identity, and never extends hp.weak_remainder to
inactive labels. -/
theorem actualLinearBlock_finite_padding (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (P : LinearProfileFamily) (u : ℕ → EnergyState)
    {L J : ℕ} (hLJ : L ≤ J) (N n : ℕ) (hcount : P.count = (N : WithTop ℕ)) :
    actualLinearBlock hDensity hSob P L J n =
      actualLinearBlock hDensity hSob P (min L N) (min J N) n := by
  rw [actualLinearBlock_eq_remainder_sub hDensity hSob P u hLJ n,
    actualLinearBlock_eq_remainder_sub hDensity hSob P u (min_le_min_right N hLJ) n]
  rw [profileRemainder_eq_min_finite hDensity hSob P u N L n hcount,
    profileRemainder_eq_min_finite hDensity hSob P u N J n hcount]

end HartreeF.R2SquareTail
