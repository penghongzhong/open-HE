import FCrossContinuityInputBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A bounded-set modulus for each literal cross derivative placement.
Its exponent (3-alpha)/3 is intentionally coarser than the sharper written proof. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.CrossContinuity
open ForcingDomain WeakHartreeChain DerivativeMajorization GradientMajorants TimeHolder CompactCross

def boundedModulus (α : ℝ) (M : ℝ≥0) (d : ℝ≥0∞) : ℝ≥0∞ :=
  (M : ℝ≥0∞)^(2*α) * (M : ℝ≥0∞)^(4 : ℝ) * d+
  (M : ℝ≥0∞)^(2*α) * (M : ℝ≥0∞)^(3 : ℝ) * M * d+
  (M : ℝ≥0∞)^(5*α/3) * (M : ℝ≥0∞)^(4-theta α) * M *
    (M : ℝ≥0∞)^(α/3) * d^theta α

theorem boundedModulus_ne_top {α : ℝ} (ha : 0<α) (ha3 : α<3) (M : ℝ≥0)
    {d : ℝ≥0∞} (hd : d≠∞) : boundedModulus α M d ≠ ∞ := by
  have h2 : 0≤2*α := by positivity
  have h5 : 0≤5*α/3 := by positivity
  have h3 : 0≤α/3 := by positivity
  have ht : 0≤theta α := by dsimp [theta]; linarith
  have h4 : 0≤4-theta α := by dsimp [theta]; linarith
  unfold boundedModulus
  finiteness

/-- Positive Hölder exponent at every point of the entire open interval. -/
theorem boundedModulus_tendsto_zero {α : ℝ} (ha : 0<α) (ha3 : α<3) (M : ℝ≥0) :
    Tendsto (boundedModulus α M) (𝓝 0) (𝓝 0) := by
  have h2 : 0≤2*α := by positivity
  have h5 : 0≤5*α/3 := by positivity
  have h3 : 0≤α/3 := by positivity
  have ht : 0<theta α := by dsimp [theta]; linarith
  have h4 : 0≤4-theta α := by dsimp [theta]; linarith
  have hc1 : (M : ℝ≥0∞)^(2*α)*(M : ℝ≥0∞)^(4 : ℝ) ≠ ∞ := by finiteness
  have hc2 : (M : ℝ≥0∞)^(2*α)*(M : ℝ≥0∞)^(3 : ℝ)*M ≠ ∞ := by finiteness
  have hc3 : (M : ℝ≥0∞)^(5*α/3)*(M : ℝ≥0∞)^(4-theta α)*M*(M : ℝ≥0∞)^(α/3) ≠ ∞ := by finiteness
  have h1 := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc1 (by norm_num : (0:ℝ)<1)
  have h2' := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc2 (by norm_num : (0:ℝ)<1)
  have h3' := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hc3 ht
  unfold boundedModulus
  convert (h1.add h2').add h3' using 1 <;> simp only [ENNReal.rpow_one, zero_add]

/-- Quantitative continuity from actual bounded V=L-infinity L6, S=L10 L10,
and directional W=L10 L(30/13) input norms. The value energy difference is
merely bounded through the original values. No small energy difference appears. -/
theorem separate_cross_bounded_continuity {α c : ℝ} (hHLS : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (u U h H v V k K : ℝ → Space → ℂ),
      JointInputs u U h H v V k K →
      (∀ᵐ t ∂(volume : Measure ℝ), SliceInputs (u t) (U t) (h t) (H t) (v t) (V t) (k t) (K t)) →
      ∀ (M d : ℝ≥0),
      valueSize ∞ 6 u U v V ≤ M → valueSize 10 10 u U v V ≤ M → referenceSize H K ≤ M →
      changeSize 10 10 u U v V ≤ d → changeSize 10 (ENNReal.ofReal (30/13 : ℝ)) h H k K ≤ d →
      forcingNorm (innerCross α c u h v-innerCross α c U H V) ≠ ∞ ∧
      forcingNorm (outerCross α c u v k-outerCross α c U V K) ≠ ∞ ∧
      forcingNorm (innerCross α c u h v-innerCross α c U H V) ≤ (C : ℝ≥0∞)*boundedModulus α M d ∧
      forcingNorm (outerCross α c u v k-outerCross α c U V K) ≤ (C : ℝ≥0∞)*boundedModulus α M d := by
  obtain ⟨C,hC⟩ := cross_pair_mixed_difference_budget hHLS
  refine ⟨C,?_⟩
  intro u U h H v V k K hJ hs M d hV hS hW hdu hdh
  obtain ⟨hA6,hA10,hB6,hB10,hY,hZ⟩ := real_envelope_input_bounds hJ hs
  have hA6' := hA6.trans hV
  have hA10' := hA10.trans hS
  have hB6' := hB6.trans hV
  have hB10' := hB10.trans hdu
  have hY' := hY.trans hW
  have hZ' := hZ.trans hdh
  have ha := hHLS.order_pos
  have ha3 := hHLS.order_lt_three
  have h2 : 0≤2*α := by positivity
  have h5 : 0≤5*α/3 := by positivity
  have h3 : 0≤α/3 := by positivity
  have ht : 0≤theta α := by dsimp [theta]; linarith
  have h4 : 0≤4-theta α := by dsimp [theta]; linarith
  have hb : crossBudget α u U h H v V k K ≤ boundedModulus α M d := by
    unfold crossBudget threeWeightBudget boundedModulus
    gcongr
  obtain ⟨hi,ho⟩ := hC u U h H v V k K hJ hs
  have hi' := hi.trans (mul_le_mul' le_rfl hb)
  have ho' := ho.trans (mul_le_mul' le_rfl hb)
  have hfin : (C : ℝ≥0∞)*boundedModulus α M d ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (boundedModulus_ne_top ha ha3 M ENNReal.coe_ne_top)
  exact ⟨ne_top_of_le_ne_top hfin hi',ne_top_of_le_ne_top hfin ho',hi',ho'⟩

#print axioms boundedModulus_ne_top
#print axioms boundedModulus_tendsto_zero
#print axioms separate_cross_bounded_continuity
end HartreeF.CrossContinuity
