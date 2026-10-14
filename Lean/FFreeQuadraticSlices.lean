import FFreeIntegralL2Compatibility
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Fixed-three-dimensional quadratic change of variables for the F free flow.
This file is an uncompiled static candidate. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory FourierTransform Filter Set
open scoped BigOperators ENNReal
namespace HartreeF.FreeLocalCompactness
open FreeFlow

/-- The time-frequency coordinate is cycles/unit: minus two pi times radius squared. -/
def quadraticMap (k : Fin 3) (ξ : V) : V :=
  WithLp.toLp 2 (Function.update (fun j => ξ j) k (-2 * Real.pi * ‖ξ‖ ^ 2))

@[simp] theorem quadraticMap_same (k : Fin 3) (ξ : V) :
    quadraticMap k ξ k = -2 * Real.pi * ‖ξ‖ ^ 2 := by
  simp [quadraticMap]

@[simp] theorem quadraticMap_other (k j : Fin 3) (hjk : j ≠ k) (ξ : V) :
    quadraticMap k ξ j = ξ j := by
  simp [quadraticMap, Function.update_of_ne hjk]

/-- The explicit derivative: identity rows except for row k. -/
def quadraticDerivative (k : Fin 3) (ξ : V) : V →L[ℝ] V :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun j => if j = k then
      (-4 * Real.pi) • innerSL ℝ ξ else PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)

@[simp] theorem quadraticDerivative_apply (k : Fin 3) (ξ h : V) (j : Fin 3) :
    quadraticDerivative k ξ h j =
      if j = k then -4 * Real.pi * inner ℝ ξ h else h j := by
  by_cases hj : j = k <;> simp [quadraticDerivative, hj]

/-- The actual derivative, rather than an assumed Jacobian. -/
theorem quadraticMap_hasFDerivAt (k : Fin 3) (ξ : V) :
    HasFDerivAt (quadraticMap k) (quadraticDerivative k ξ) ξ := by
  have hq : HasFDerivAt (fun x : V => -2 * Real.pi * ‖x‖ ^ 2)
      ((-4 * Real.pi) • innerSL ℝ ξ) ξ := by
    convert (hasStrictFDerivAt_norm_sq ξ).hasFDerivAt.const_mul (-2 * Real.pi) using 1
    ext h
    simp only [smul_apply, smul_eq_mul]
    ring
  have hc : HasFDerivAt
      (fun x : V => fun j : Fin 3 => if j = k then -2 * Real.pi * ‖x‖ ^ 2 else x j)
      (ContinuousLinearMap.pi (fun j => if j = k then
        (-4 * Real.pi) • innerSL ℝ ξ else PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j)) ξ := by
    apply hasFDerivAt_pi.2
    intro j
    by_cases hj : j = k
    · simpa only [hj, ite_true] using hq
    · let P : V →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j
      have hp : HasFDerivAt (fun x : V => x j) P ξ := P.hasFDerivAt
      simpa only [hj, ite_false] using hp
  let L : (Fin 3 → ℝ) →L[ℝ] V :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  convert L.hasFDerivAt.comp ξ hc using 1
  · ext x j
    exact Function.update_apply (fun i => x i) k (-2 * Real.pi * ‖x‖ ^ 2) j
  · ext h j
    by_cases hj : j = k <;> simp [quadraticDerivative, L, hj]

theorem quadraticMap_continuous (k : Fin 3) : Continuous (quadraticMap k) :=
  continuous_iff_continuousAt.2 (fun ξ => (quadraticMap_hasFDerivAt k ξ).continuousAt)

theorem quadraticDerivative_toMatrix (k : Fin 3) (ξ : V) :
    LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 3)) (PiLp.basisFun 2 ℝ (Fin 3))
      (quadraticDerivative k ξ).toLinearMap =
      (1 : Matrix (Fin 3) (Fin 3) ℝ).updateRow k (fun j => -4 * Real.pi * ξ j) := by
  ext i j
  by_cases hik : i = k
  · subst i
    rw [Matrix.updateRow_self]
    simp [LinearMap.toMatrix_apply, EuclideanSpace.inner_single_right]
  · rw [Matrix.updateRow_ne hik]
    simp [LinearMap.toMatrix_apply, hik, Matrix.one_apply]

theorem quadraticDerivative_det (k : Fin 3) (ξ : V) :
    (quadraticDerivative k ξ).det = -4 * Real.pi * ξ k := by
  change LinearMap.det (quadraticDerivative k ξ).toLinearMap = _
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3)),
    quadraticDerivative_toMatrix]
  have hr : (fun j : Fin 3 => -4 * Real.pi * ξ j) =
      ∑ j : Fin 3, (-4 * Real.pi * ξ j) • (1 : Matrix (Fin 3) (Fin 3) ℝ) j := by
    ext i
    simp [Matrix.one_apply, Finset.sum_apply, eq_comm]
  rw [hr, Matrix.det_updateRow_sum]
  simp

theorem quadraticDerivative_abs_det (k : Fin 3) (ξ : V) :
    |(quadraticDerivative k ξ).det| = 4 * Real.pi * |ξ k| := by
  rw [quadraticDerivative_det, abs_mul, abs_mul]
  simp [abs_of_pos Real.pi_pos]

/-- Positive and negative coordinate halfspaces, indexed by a Boolean sign. -/
def signedHalfspace (k : Fin 3) (σ : Bool) : Set V :=
  {ξ | if σ then 0 < ξ k else ξ k < 0}

theorem signedHalfspace_measurable (k : Fin 3) (σ : Bool) :
    MeasurableSet (signedHalfspace k σ) := by
  cases σ <;> simp only [signedHalfspace, Bool.false_eq_true, ite_false, ite_true]
  · exact isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  · exact isOpen_lt continuous_const (by fun_prop) |>.measurableSet

theorem coordinate_ne_zero_of_mem_halfspace {k : Fin 3} {σ : Bool} {ξ : V}
    (hξ : ξ ∈ signedHalfspace k σ) : ξ k ≠ 0 := by
  cases σ <;> simp only [signedHalfspace, mem_ofPred_eq, Bool.false_eq_true,
    ite_false, ite_true] at hξ
  · exact ne_of_lt hξ
  · exact ne_of_gt hξ

/-- The explicit inverse is defined everywhere; its inverse identities are
only asserted on the correct signed branch. -/
def quadraticInverse (k : Fin 3) (σ : Bool) (η : V) : V :=
  WithLp.toLp 2 (Function.update (fun j => η j) k
    ((if σ then (1 : ℝ) else -1) *
      Real.sqrt (-η k / (2 * Real.pi) - ∑ j ∈ Finset.univ.erase k, (η j) ^ 2)))

theorem quadraticInverse_continuous (k : Fin 3) (σ : Bool) :
    Continuous (quadraticInverse k σ) := by
  unfold quadraticInverse
  fun_prop

theorem quadraticInverse_left (k : Fin 3) (σ : Bool) {ξ : V}
    (hξ : ξ ∈ signedHalfspace k σ) :
    quadraticInverse k σ (quadraticMap k ξ) = ξ := by
  have hs : -quadraticMap k ξ k / (2 * Real.pi) -
      ∑ j ∈ Finset.univ.erase k, (quadraticMap k ξ j) ^ 2 = (ξ k) ^ 2 := by
    rw [quadraticMap_same]
    have he : (∑ j ∈ Finset.univ.erase k, (quadraticMap k ξ j) ^ 2) =
        ∑ j ∈ Finset.univ.erase k, (ξ j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [quadraticMap_other k j (Finset.mem_erase.mp hj).1]
    rw [he]
    have hn := Finset.add_sum_erase Finset.univ (fun j => (ξ j) ^ 2) (Finset.mem_univ k)
    rw [EuclideanSpace.real_norm_sq_eq, ← hn]
    field_simp [Real.pi_ne_zero]
    ring
  ext j
  by_cases hj : j = k
  · subst j
    simp only [quadraticInverse, PiLp.toLp_apply, Function.update_self]
    rw [hs, Real.sqrt_sq_eq_abs]
    cases σ <;> simp only [signedHalfspace, mem_ofPred_eq, Bool.false_eq_true,
      ite_false, ite_true] at hξ ⊢
    · rw [abs_of_neg hξ]
      ring
    · rw [abs_of_pos hξ, one_mul]
  · simp [quadraticInverse, Function.update_of_ne hj, quadraticMap_other k j hj]

theorem quadraticMap_injOn (k : Fin 3) (σ : Bool) :
    InjOn (quadraticMap k) (signedHalfspace k σ) := by
  intro ξ hξ ζ hζ h
  calc
    ξ = quadraticInverse k σ (quadraticMap k ξ) := (quadraticInverse_left k σ hξ).symm
    _ = quadraticInverse k σ (quadraticMap k ζ) := congrArg _ h
    _ = ζ := quadraticInverse_left k σ hζ

theorem quadraticInverse_right (k : Fin 3) (σ : Bool) {S : Set V}
    (hS : S ⊆ signedHalfspace k σ) {η : V} (hη : η ∈ quadraticMap k '' S) :
    quadraticMap k (quadraticInverse k σ η) = η := by
  rcases hη with ⟨ξ, hξ, rfl⟩
  rw [quadraticInverse_left k σ (hS hξ)]

theorem quadraticMap_image_measurable (k : Fin 3) (σ : Bool) {S : Set V}
    (hS : MeasurableSet S) (hSH : S ⊆ signedHalfspace k σ) :
    MeasurableSet (quadraticMap k '' S) :=
  measurable_image_of_fderivWithin hS
    (fun ξ _ => (quadraticMap_hasFDerivAt k ξ).hasFDerivWithinAt)
    ((quadraticMap_injOn k σ).mono hSH)

/-- The least dominant coordinate, with every tie assigned explicitly. -/
def dominantIndex (ξ : V) : Fin 3 :=
  if |ξ 1| ≤ |ξ 0| ∧ |ξ 2| ≤ |ξ 0| then 0 else
    if |ξ 2| ≤ |ξ 1| then 1 else 2

theorem dominantIndex_measurable : Measurable dominantIndex := by
  have hm (j : Fin 3) : Measurable (fun ξ : V => |ξ j|) := by fun_prop
  unfold dominantIndex
  exact Measurable.ite
    (p := fun ξ : V => |ξ 1| ≤ |ξ 0| ∧ |ξ 2| ≤ |ξ 0|)
    ((measurableSet_le (hm 1) (hm 0)).inter (measurableSet_le (hm 2) (hm 0)))
    measurable_const
    (Measurable.ite (p := fun ξ : V => |ξ 2| ≤ |ξ 1|)
      (measurableSet_le (hm 2) (hm 1)) measurable_const measurable_const)

theorem dominantIndex_dominates (ξ : V) (j : Fin 3) :
    |ξ j| ≤ |ξ (dominantIndex ξ)| := by
  by_cases h₀ : |ξ 1| ≤ |ξ 0| ∧ |ξ 2| ≤ |ξ 0|
  · rw [dominantIndex, ite_eq_left h₀]
    fin_cases j
    · exact le_rfl
    · exact h₀.1
    · exact h₀.2
  · rw [dominantIndex, ite_eq_right h₀]
    by_cases h₁ : |ξ 2| ≤ |ξ 1|
    · rw [ite_eq_left h₁]
      fin_cases j
      · by_contra h
        have h10 : |ξ 1| ≤ |ξ 0| := le_of_lt (lt_of_not_ge h)
        exact h₀ ⟨h10, h₁.trans h10⟩
      · exact le_rfl
      · exact h₁
    · rw [ite_eq_right h₁]
      have h12 : |ξ 1| ≤ |ξ 2| := le_of_lt (lt_of_not_ge h₁)
      fin_cases j
      · by_contra h
        have h20 : |ξ 2| ≤ |ξ 0| := le_of_lt (lt_of_not_ge h)
        exact h₀ ⟨h12.trans h20, h20⟩
      · exact h12
      · exact le_rfl

/-- Quantitative dominance, including the exact three-dimensional constant. -/
theorem norm_le_sqrt_three_mul_dominant (ξ : V) :
    ‖ξ‖ ≤ Real.sqrt 3 * |ξ (dominantIndex ξ)| := by
  have hs : ‖ξ‖ ^ 2 ≤ 3 * |ξ (dominantIndex ξ)| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin 3, |ξ (dominantIndex ξ)| ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 (dominantIndex_dominates ξ j)
      _ = _ := by simp
  have h3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  apply (sq_le_sq₀ (norm_nonneg ξ)
    (mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (abs_nonneg _))).mp
  rw [mul_pow, h3]
  exact hs

theorem dominantIndex_ne_zero {ξ : V} (hξ : ξ ≠ 0) : ξ (dominantIndex ξ) ≠ 0 := by
  intro h
  have hn := norm_le_sqrt_three_mul_dominant ξ
  rw [h, abs_zero, mul_zero] at hn
  exact hξ (norm_eq_zero.mp (le_antisymm hn (norm_nonneg ξ)))

abbrev ConeIndex := Fin 3 × Bool

def dominantCone (c : ConeIndex) : Set V :=
  {ξ | dominantIndex ξ = c.1} ∩ signedHalfspace c.1 c.2

theorem dominantCone_measurable (c : ConeIndex) : MeasurableSet (dominantCone c) :=
  (measurableSet_eq_fun dominantIndex_measurable measurable_const).inter
    (signedHalfspace_measurable c.1 c.2)

theorem dominantCone_disjoint {c d : ConeIndex} (hcd : c ≠ d) :
    Disjoint (dominantCone c) (dominantCone d) := by
  apply disjoint_left.2
  intro ξ hξ hη
  have hk : c.1 = d.1 := hξ.1.symm.trans hη.1
  rcases c with ⟨k, σ⟩
  rcases d with ⟨j, τ⟩
  dsimp at hk
  subst j
  cases σ <;> cases τ
  · exact hcd rfl
  · have h₁ : ξ k < 0 := hξ.2
    have h₂ : 0 < ξ k := hη.2
    exact (lt_asymm h₁ h₂)
  · have h₁ : 0 < ξ k := hξ.2
    have h₂ : ξ k < 0 := hη.2
    exact (lt_asymm h₁ h₂)
  · exact hcd rfl

theorem dominantCone_cover {ξ : V} (hξ : ξ ≠ 0) : ∃ c : ConeIndex, ξ ∈ dominantCone c := by
  rcases lt_or_gt_of_ne (dominantIndex_ne_zero hξ) with hn | hp
  · exact ⟨(dominantIndex ξ, false), rfl, hn⟩
  · exact ⟨(dominantIndex ξ, true), rfl, hp⟩

theorem dominantCone_coordinate_bound {c : ConeIndex} {ξ : V}
    (hξ : ξ ∈ dominantCone c) : ‖ξ‖ ≤ Real.sqrt 3 * |ξ c.1| := by
  have hk : dominantIndex ξ = c.1 := hξ.1
  rw [← hk]
  exact norm_le_sqrt_three_mul_dominant ξ

/-- The honest measurable annular cone, with a finite outer radius. -/
def truncatedCone (c : ConeIndex) (N m : ℝ) : Set V :=
  dominantCone c ∩ {ξ | N < ‖ξ‖ ∧ ‖ξ‖ ≤ m}

theorem truncatedCone_measurable (c : ConeIndex) (N m : ℝ) :
    MeasurableSet (truncatedCone c N m) :=
  (dominantCone_measurable c).inter
    ((isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isClosed_le continuous_norm continuous_const).measurableSet)

theorem truncatedCone_subset_halfspace (c : ConeIndex) (N m : ℝ) :
    truncatedCone c N m ⊆ signedHalfspace c.1 c.2 := fun _ h => h.1.2


/-- The physical fixed-coordinate modulation has modulus one. -/
def slicePhase (k : Fin 3) (b : ℝ) (ξ : V) : ℂ :=
  Complex.exp (((2 * Real.pi * b * ξ k : ℝ) : ℂ) * Complex.I)

theorem slicePhase_norm (k : Fin 3) (b : ℝ) (ξ : V) : ‖slicePhase k b ξ‖ = 1 := by
  simp [slicePhase, Complex.norm_exp]

def quadraticJacobian (k : Fin 3) (ξ : V) : ℝ := 4 * Real.pi * |ξ k|

theorem quadraticJacobian_pos {k : Fin 3} {σ : Bool} {ξ : V}
    (hξ : ξ ∈ signedHalfspace k σ) : 0 < quadraticJacobian k ξ := by
  unfold quadraticJacobian
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (abs_pos.mpr (coordinate_ne_zero_of_mem_halfspace hξ))

/-- Raw transformed amplitude; its inverse uses a chosen strongly measurable
representative, never an arbitrary equivalence-class representative composed
with an unproved quasi-measure-preserving map. -/
def rawSliceAmplitude (k : Fin 3) (σ : Bool) (a : V → ℂ) (b : ℝ) (η : V) : ℂ :=
  slicePhase k b (quadraticInverse k σ η) * a (quadraticInverse k σ η) /
    (quadraticJacobian k (quadraticInverse k σ η) : ℂ)

def sliceAmplitude (k : Fin 3) (σ : Bool) (S : Set V) (a : V → ℂ) (b : ℝ) : V → ℂ :=
  (quadraticMap k '' S).indicator (rawSliceAmplitude k σ a b)

theorem rawSliceAmplitude_measurable (k : Fin 3) (σ : Bool) {a : V → ℂ}
    (ha : StronglyMeasurable a) (b : ℝ) :
    Measurable (rawSliceAmplitude k σ a b) := by
  have hi := (quadraticInverse_continuous k σ).measurable
  have hm := ha.measurable.comp hi
  unfold rawSliceAmplitude slicePhase quadraticJacobian
  fun_prop

theorem sliceAmplitude_stronglyMeasurable (k : Fin 3) (σ : Bool) {S : Set V}
    (hs : MeasurableSet S) (hsh : S ⊆ signedHalfspace k σ) {a : V → ℂ}
    (ha : StronglyMeasurable a) (b : ℝ) :
    StronglyMeasurable (sliceAmplitude k σ S a b) :=
  ((rawSliceAmplitude_measurable k σ ha b).indicator
    (quadraticMap_image_measurable k σ hs hsh)).stronglyMeasurable

theorem jacobian_smul_rawSliceAmplitude (k : Fin 3) (σ : Bool) (a : V → ℂ)
    (b : ℝ) {ξ : V} (hξ : ξ ∈ signedHalfspace k σ) :
    |(quadraticDerivative k ξ).det| • rawSliceAmplitude k σ a b (quadraticMap k ξ) =
      slicePhase k b ξ * a ξ := by
  rw [quadraticDerivative_abs_det]
  change quadraticJacobian k ξ • rawSliceAmplitude k σ a b (quadraticMap k ξ) = _
  rw [rawSliceAmplitude, quadraticInverse_left k σ hξ, Complex.real_smul]
  have hj : (quadraticJacobian k ξ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (quadraticJacobian_pos hξ).ne'
  field_simp [hj]

theorem jacobian_sq_rawSliceAmplitude (k : Fin 3) (σ : Bool) (a : V → ℂ)
    (b : ℝ) {ξ : V} (hξ : ξ ∈ signedHalfspace k σ) :
    |(quadraticDerivative k ξ).det| *
        ‖rawSliceAmplitude k σ a b (quadraticMap k ξ)‖ ^ 2 =
      ‖a ξ‖ ^ 2 / quadraticJacobian k ξ := by
  rw [quadraticDerivative_abs_det]
  change quadraticJacobian k ξ *
    ‖rawSliceAmplitude k σ a b (quadraticMap k ξ)‖ ^ 2 = _
  rw [rawSliceAmplitude, quadraticInverse_left k σ hξ,
    norm_div, norm_mul, slicePhase_norm, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (quadraticJacobian_pos hξ)]
  field_simp [(quadraticJacobian_pos hξ).ne']

/-- Genuine transformed L1 domain, obtained by the actual Jacobian equivalence. -/
theorem sliceAmplitude_integrable (k : Fin 3) (σ : Bool) {S : Set V}
    (hs : MeasurableSet S) (hsh : S ⊆ signedHalfspace k σ) {a : V → ℂ}
    (has : StronglyMeasurable a) (ha : IntegrableOn a S) (b : ℝ) :
    Integrable (sliceAmplitude k σ S a b) := by
  apply IntegrableOn.integrable_indicator
  · apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
      (fun ξ _ => (quadraticMap_hasFDerivAt k ξ).hasFDerivWithinAt)
      ((quadraticMap_injOn k σ).mono hsh) (rawSliceAmplitude k σ a b)).2
    have hm : IntegrableOn (fun ξ => slicePhase k b ξ * a ξ) S := by
      apply Integrable.mono ha
      · have hphase : Continuous (slicePhase k b) := by
          unfold slicePhase
          fun_prop
        exact (hphase.stronglyMeasurable.mul has).aestronglyMeasurable
      · exact Eventually.of_forall (fun ξ => by rw [norm_mul, slicePhase_norm, one_mul])
    apply hm.congr
    filter_upwards [ae_restrict_mem hs] with ξ hξ
    exact (jacobian_smul_rawSliceAmplitude k σ a b (hsh hξ)).symm
  · exact quadraticMap_image_measurable k σ hs hsh

/-- A positive coordinate lower bound makes the reciprocal-Jacobian square
weight integrable. This is a real input-domain lemma, not a smoothing premise. -/
theorem reciprocalJacobian_sq_integrable (k : Fin 3) {S : Set V}
    (hs : MeasurableSet S) {a : V → ℂ} (has : StronglyMeasurable a)
    (ha2 : MemLp a 2 (volume.restrict S)) {δ : ℝ} (hδ : 0 < δ)
    (hSδ : ∀ ξ ∈ S, δ ≤ |ξ k|) :
    IntegrableOn (fun ξ => ‖a ξ‖ ^ 2 / quadraticJacobian k ξ) S := by
  have hi : IntegrableOn (fun ξ => ‖a ξ‖ ^ 2) S :=
    (memLp_two_iff_integrable_sq_norm ha2.aestronglyMeasurable).mp ha2
  apply (hi.div_const (4 * Real.pi * δ)).mono'
  · have hm : Measurable (fun ξ => ‖a ξ‖ ^ 2 / quadraticJacobian k ξ) := by
      have hm := has.measurable
      unfold quadraticJacobian
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hs] with ξ hξ
    have hJ : 0 < quadraticJacobian k ξ := by
      unfold quadraticJacobian
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (hδ.trans_le (hSδ ξ hξ))
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hJ.le)]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (hSδ ξ hξ) (by positivity)

/-- Genuine transformed L2 domain precedes integral Plancherel. -/
theorem sliceAmplitude_memLp (k : Fin 3) (σ : Bool) {S : Set V}
    (hs : MeasurableSet S) (hsh : S ⊆ signedHalfspace k σ) {a : V → ℂ}
    (has : StronglyMeasurable a) (ha2 : MemLp a 2 (volume.restrict S))
    {δ : ℝ} (hδ : 0 < δ) (hSδ : ∀ ξ ∈ S, δ ≤ |ξ k|) (b : ℝ) :
    MemLp (sliceAmplitude k σ S a b) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (sliceAmplitude_stronglyMeasurable k σ hs hsh has b).aestronglyMeasurable).2
  have hi : IntegrableOn (fun η => ‖rawSliceAmplitude k σ a b η‖ ^ 2)
      (quadraticMap k '' S) := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
      (fun ξ _ => (quadraticMap_hasFDerivAt k ξ).hasFDerivWithinAt)
      ((quadraticMap_injOn k σ).mono hsh)
      (fun η => ‖rawSliceAmplitude k σ a b η‖ ^ 2)).2
    apply (reciprocalJacobian_sq_integrable k hs has ha2 hδ hSδ).congr
    filter_upwards [ae_restrict_mem hs] with ξ hξ
    exact (jacobian_sq_rawSliceAmplitude k σ a b (hsh hξ)).symm
  convert hi.integrable_indicator (quadraticMap_image_measurable k σ hs hsh) using 1
  ext η
  by_cases hη : η ∈ quadraticMap k '' S <;> simp [sliceAmplitude, hη]

/-- Exact square identity for the transformed amplitude. -/
theorem sliceAmplitude_square_integral (k : Fin 3) (σ : Bool) {S : Set V}
    (hs : MeasurableSet S) (hsh : S ⊆ signedHalfspace k σ)
    (a : V → ℂ) (b : ℝ) :
    (∫ η, ‖sliceAmplitude k σ S a b η‖ ^ 2) =
      ∫ ξ in S, ‖a ξ‖ ^ 2 / quadraticJacobian k ξ := by
  have hind : (fun η => ‖sliceAmplitude k σ S a b η‖ ^ 2) =
      (quadraticMap k '' S).indicator (fun η => ‖rawSliceAmplitude k σ a b η‖ ^ 2) := by
    ext η
    by_cases hη : η ∈ quadraticMap k '' S <;> simp [sliceAmplitude, hη]
  rw [hind, integral_indicator (quadraticMap_image_measurable k σ hs hsh),
    integral_image_eq_integral_abs_det_fderiv_smul volume hs
      (fun ξ _ => (quadraticMap_hasFDerivAt k ξ).hasFDerivWithinAt)
      ((quadraticMap_injOn k σ).mono hsh)]
  apply setIntegral_congr_fun hs
  intro ξ hξ
  exact jacobian_sq_rawSliceAmplitude k σ a b (hsh hξ)

/-- Slice Plancherel for the transformed inverse integral. Its actual L1 and
L2 domains have both been constructed above. -/
theorem inverseSliceAmplitude_plancherel (k : Fin 3) (σ : Bool) {S : Set V}
    (hs : MeasurableSet S) (hsh : S ⊆ signedHalfspace k σ) {a : V → ℂ}
    (has : StronglyMeasurable a) (ha : IntegrableOn a S)
    (ha2 : MemLp a 2 (volume.restrict S))
    {δ : ℝ} (hδ : 0 < δ) (hSδ : ∀ ξ ∈ S, δ ≤ |ξ k|) (b : ℝ) :
    (∫ y, ‖𝓕⁻ (sliceAmplitude k σ S a b) y‖ ^ 2) =
      ∫ ξ in S, ‖a ξ‖ ^ 2 / quadraticJacobian k ξ := by
  rw [inverseFourierIntegral_plancherel
    (sliceAmplitude_integrable k σ hs hsh has ha b)
    (sliceAmplitude_memLp k σ hs hsh has ha2 hδ hSδ b),
    sliceAmplitude_square_integral k σ hs hsh]


/-- Insert a fixed physical coordinate; the replaced coordinate of y is time. -/
def spatialSlice (k : Fin 3) (b : ℝ) (y : V) : V :=
  WithLp.toLp 2 (Function.update (fun j => y j) k b)

@[simp] theorem spatialSlice_same (k : Fin 3) (b : ℝ) (y : V) :
    spatialSlice k b y k = b := by simp [spatialSlice]

@[simp] theorem spatialSlice_other (k j : Fin 3) (hjk : j ≠ k) (b : ℝ) (y : V) :
    spatialSlice k b y j = y j := by simp [spatialSlice, hjk]

def inverseKernel (ξ x : V) : ℂ :=
  Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I)

theorem inverseKernel_norm (ξ x : V) : ‖inverseKernel ξ x‖ = 1 := by
  simp [inverseKernel, Complex.norm_exp]

theorem quadratic_inner_identity (k : Fin 3) (b : ℝ) (ξ y : V) :
    inner ℝ (quadraticMap k ξ) y + b * ξ k =
      inner ℝ ξ (spatialSlice k b y) - 2 * Real.pi * y k * ‖ξ‖ ^ 2 := by
  have inner_sum (u v : V) : inner ℝ u v = ∑ j, u j * v j := by
    simp [PiLp.inner_apply, mul_comm]
  rw [inner_sum, inner_sum]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => quadraticMap k ξ j * y j) (Finset.mem_univ k),
    ← Finset.add_sum_erase Finset.univ
      (fun j => ξ j * spatialSlice k b y j) (Finset.mem_univ k)]
  rw [quadraticMap_same, spatialSlice_same]
  have he : (∑ j ∈ Finset.univ.erase k, quadraticMap k ξ j * y j) =
      ∑ j ∈ Finset.univ.erase k, ξ j * spatialSlice k b y j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := (Finset.mem_erase.mp hj).1
    rw [quadraticMap_other k j hjk, spatialSlice_other k j hjk]
  rw [he]
  ring

theorem quadratic_kernel_identity (k : Fin 3) (b : ℝ) (ξ y : V) :
    inverseKernel (quadraticMap k ξ) y * slicePhase k b ξ =
      inverseKernel ξ (spatialSlice k b y) * phase (y k) ξ := by
  rw [inverseKernel, slicePhase, inverseKernel, phase, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hi := congrArg Complex.ofReal (quadratic_inner_identity k b ξ y)
  push_cast at hi ⊢
  linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hi

/-- The actual Bochner change-of-variables identity. The domain lemmas above
supply L1 and L2 before this identity is used in Plancherel. -/
theorem inverseSliceAmplitude_eq_integralEvolution (k : Fin 3) (σ : Bool) {S : Set V}
    (hs : MeasurableSet S) (hsh : S ⊆ signedHalfspace k σ)
    (a : V → ℂ) (b : ℝ) (y : V) :
    𝓕⁻ (sliceAmplitude k σ S a b) y =
      integralEvolution (S.indicator a) (y k) (spatialSlice k b y) := by
  have him := quadraticMap_image_measurable k σ hs hsh
  calc
    _ = ∫ η in quadraticMap k '' S, inverseKernel η y * rawSliceAmplitude k σ a b η := by
      rw [Real.fourierInv_eq', ← integral_indicator him]
      apply integral_congr_ae
      exact Eventually.of_forall (fun η => by
        by_cases hη : η ∈ quadraticMap k '' S <;>
          simp [sliceAmplitude, inverseKernel, hη, smul_eq_mul])
    _ = ∫ ξ in S, |(quadraticDerivative k ξ).det| •
        (inverseKernel (quadraticMap k ξ) y * rawSliceAmplitude k σ a b (quadraticMap k ξ)) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hs
        (fun ξ _ => (quadraticMap_hasFDerivAt k ξ).hasFDerivWithinAt)
        ((quadraticMap_injOn k σ).mono hsh) _
    _ = ∫ ξ in S, inverseKernel ξ (spatialSlice k b y) * (phase (y k) ξ * a ξ) := by
      apply setIntegral_congr_fun hs
      intro ξ hξ
      calc
        _ = inverseKernel (quadraticMap k ξ) y *
            (|(quadraticDerivative k ξ).det| • rawSliceAmplitude k σ a b (quadraticMap k ξ)) := by
          simp only [Complex.real_smul]
          ring
        _ = inverseKernel (quadraticMap k ξ) y * (slicePhase k b ξ * a ξ) := by
          rw [jacobian_smul_rawSliceAmplitude k σ a b (hsh hξ)]
        _ = (inverseKernel (quadraticMap k ξ) y * slicePhase k b ξ) * a ξ := by ring
        _ = _ := by rw [quadratic_kernel_identity]; ring
    _ = integralEvolution (S.indicator a) (y k) (spatialSlice k b y) := by
      rw [integralEvolution, Real.fourierInv_eq', ← integral_indicator hs]
      apply integral_congr_ae
      exact Eventually.of_forall (fun ξ => by
        by_cases hξ : ξ ∈ S <;> simp [inverseKernel, hξ, smul_eq_mul])

/-- Exact every-b trace identity for U_S, the explicit Fourier integral. No
arbitrary-b trace assertion about a canonical freeJoint representative occurs. -/
theorem integralEvolution_truncated_slice_plancherel (k : Fin 3) (σ : Bool) {S : Set V}
    (hs : MeasurableSet S) (hsh : S ⊆ signedHalfspace k σ) {a : V → ℂ}
    (has : StronglyMeasurable a) (ha : IntegrableOn a S)
    (ha2 : MemLp a 2 (volume.restrict S))
    {δ : ℝ} (hδ : 0 < δ) (hSδ : ∀ ξ ∈ S, δ ≤ |ξ k|) (b : ℝ) :
    (∫ y, ‖integralEvolution (S.indicator a) (y k) (spatialSlice k b y)‖ ^ 2) =
      ∫ ξ in S, ‖a ξ‖ ^ 2 / quadraticJacobian k ξ := by
  simp_rw [← inverseSliceAmplitude_eq_integralEvolution k σ hs hsh]
  exact inverseSliceAmplitude_plancherel k σ hs hsh has ha ha2 hδ hSδ b

theorem integralEvolution_truncated_slice_memLp (k : Fin 3) (σ : Bool) {S : Set V}
    (hs : MeasurableSet S) (hsh : S ⊆ signedHalfspace k σ) {a : V → ℂ}
    (has : StronglyMeasurable a) (ha : IntegrableOn a S)
    (ha2 : MemLp a 2 (volume.restrict S))
    {δ : ℝ} (hδ : 0 < δ) (hSδ : ∀ ξ ∈ S, δ ≤ |ξ k|) (b : ℝ) :
    MemLp (fun y => integralEvolution (S.indicator a) (y k) (spatialSlice k b y)) 2 := by
  exact MemLp.ae_eq
    (Eventually.of_forall (fun y =>
      inverseSliceAmplitude_eq_integralEvolution k σ hs hsh a b y))
    (inverseFourierIntegral_memLp
      (sliceAmplitude_integrable k σ hs hsh has ha b)
      (sliceAmplitude_memLp k σ hs hsh has ha2 hδ hSδ b))


theorem truncatedCone_measure_lt_top (c : ConeIndex) (N m : ℝ) :
    volume (truncatedCone c N m) < ∞ := by
  apply lt_of_le_of_lt (measure_mono (show truncatedCone c N m ⊆ Metric.closedBall 0 m from ?_))
    (isCompact_closedBall (0 : V) m).measure_lt_top
  intro ξ hξ
  simpa only [Metric.mem_closedBall, dist_zero_right] using hξ.2.2

theorem truncatedCone_memLp {a : V → ℂ} (ha2 : MemLp a 2)
    (c : ConeIndex) (N m : ℝ) : MemLp ((truncatedCone c N m).indicator a) 2 :=
  ha2.indicator (truncatedCone_measurable c N m).nullMeasurableSet

theorem truncatedCone_integrable {a : V → ℂ} (ha2 : MemLp a 2)
    (c : ConeIndex) (N m : ℝ) : Integrable ((truncatedCone c N m).indicator a) := by
  have : IsFiniteMeasure (volume.restrict (truncatedCone c N m)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using truncatedCone_measure_lt_top c N m⟩
  apply IntegrableOn.integrable_indicator
  · exact memLp_one_iff_integrable.mp
      (MemLp.mono_exponent (ha2.restrict (s := truncatedCone c N m))
        (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  · exact truncatedCone_measurable c N m

theorem truncatedCone_coordinate_lower (c : ConeIndex) {N m : ℝ} (_hN : 0 < N)
    {ξ : V} (hξ : ξ ∈ truncatedCone c N m) : N / Real.sqrt 3 ≤ |ξ c.1| := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply (div_le_iff₀ hs).2
  have hd := dominantCone_coordinate_bound hξ.1
  nlinarith [hξ.2.1]

/-- Quantitative weighted square bound before any spatial/time integration. -/
theorem truncatedCone_weight_bound (c : ConeIndex) {N m : ℝ} (hN : 0 < N)
    {a : V → ℂ} (has : StronglyMeasurable a) (ha2 : MemLp a 2) :
    (∫ ξ in truncatedCone c N m, ‖a ξ‖ ^ 2 / quadraticJacobian c.1 ξ) ≤
      (Real.sqrt 3 / (4 * Real.pi * N)) * ∫ ξ in truncatedCone c N m, ‖a ξ‖ ^ 2 := by
  have hδ : 0 < N / Real.sqrt (3 : ℝ) := by positivity
  have haS := ha2.restrict (s := truncatedCone c N m)
  have hs := truncatedCone_measurable c N m
  have hi := reciprocalJacobian_sq_integrable c.1 hs has haS hδ
    (fun ξ hξ => truncatedCone_coordinate_lower c hN hξ)
  have hsq := (memLp_two_iff_integrable_sq_norm haS.aestronglyMeasurable).mp haS
  rw [← integral_const_mul]
  apply integral_mono_ae hi (hsq.const_mul _)
  filter_upwards [ae_restrict_mem hs] with ξ hξ
  have hJ : 0 < quadraticJacobian c.1 ξ := quadraticJacobian_pos hξ.1.2
  have hd := truncatedCone_coordinate_lower c hN hξ
  have hbound : 1 / quadraticJacobian c.1 ξ ≤ Real.sqrt 3 / (4 * Real.pi * N) := by
    apply (div_le_div_iff₀ hJ (by positivity)).2
    unfold quadraticJacobian
    have hroot : 0 < Real.sqrt (3 : ℝ) := by positivity
    have hd' := (div_le_iff₀ hroot).mp hd
    have hm := mul_le_mul_of_nonneg_left hd' (by positivity : 0 ≤ 4 * Real.pi)
    nlinarith only [hm]
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    mul_le_mul_of_nonneg_left hbound (sq_nonneg ‖a ξ‖)

/-- The exact cone slice estimate for the explicit representative U_S. -/
theorem truncatedCone_slice_bound (c : ConeIndex) {N m : ℝ} (hN : 0 < N)
    {a : V → ℂ} (has : StronglyMeasurable a) (ha2 : MemLp a 2) (b : ℝ) :
    (∫ y, ‖integralEvolution ((truncatedCone c N m).indicator a)
      (y c.1) (spatialSlice c.1 b y)‖ ^ 2) ≤
      (Real.sqrt 3 / (4 * Real.pi * N)) * ∫ ξ in truncatedCone c N m, ‖a ξ‖ ^ 2 := by
  have hs := truncatedCone_measurable c N m
  have haS : IntegrableOn a (truncatedCone c N m) :=
    (integrable_indicator_iff hs).mp (truncatedCone_integrable ha2 c N m)
  rw [integralEvolution_truncated_slice_plancherel c.1 c.2 hs
    (truncatedCone_subset_halfspace c N m) has haS
    (ha2.restrict (s := truncatedCone c N m)) (by positivity : 0 < N / Real.sqrt (3 : ℝ))
    (fun ξ hξ => truncatedCone_coordinate_lower c hN hξ)]
  exact truncatedCone_weight_bound c hN has ha2

end HartreeF.FreeLocalCompactness
