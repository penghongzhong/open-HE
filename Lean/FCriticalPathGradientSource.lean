import FCriticalPathSourceBudgets

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 100000
set_option linter.unusedSectionVars false
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace HartreeF.CriticalJointSources
open EnergySpace CriticalPathSpace CriticalTimeSobolev TimeHolder SobolevStretch
open StationarySelfTest ForcingDomain GradientMajorants WeakHartreeProduct
attribute [local irreducible] jointFields
local instance endpoint_one_le : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
local instance endpoint_ne_top : Fact (ENNReal.ofReal (6/5 : ℝ) ≠ ∞) := ⟨ENNReal.ofReal_ne_top⟩

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
  [BorelSpace T] (μ : Measure T) [SigmaFinite μ]

theorem joint_actualGradient_finite (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (z w : CriticalPath μ) :
    mixedNorm μ volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c ((jointFields μ z).u t) ((jointFields μ z).U t)
        ((jointFields μ z).V t) - actualFullGradient alpha c ((jointFields μ w).u t)
        ((jointFields μ w).U t) ((jointFields μ w).V t)) ≠ ∞ := by
  let C : ℝ≥0 := Classical.choose (actual_full_gradient_vector_difference_bound hH)
  have hbound := (Classical.choose_spec (actual_full_gradient_vector_difference_bound hH))
    μ (jointFields μ z).u (jointFields μ w).u
    (jointFields μ z).U (jointFields μ z).V (jointFields μ w).U (jointFields μ w).V
    (joint_slices μ hDensity hSob z w)
    (jointFields μ z).joint_u.aestronglyMeasurable (jointFields μ w).joint_u.aestronglyMeasurable
    (jointFields μ z).joint_U.aestronglyMeasurable (jointFields μ z).joint_V.aestronglyMeasurable
    (jointFields μ w).joint_U.aestronglyMeasurable (jointFields μ w).joint_V.aestronglyMeasurable
  have hfinite : (C : ℝ≥0∞) * vectorDifferenceBudget alpha μ
      (jointFields μ z).u (jointFields μ w).u
      (jointFields μ z).U (jointFields μ z).V (jointFields μ w).U (jointFields μ w).V ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (joint_vectorBudget_finite μ hDensity hSob hH.order_pos hH.order_lt_three z w)
  exact ne_top_of_le_ne_top hfinite hbound

theorem exists_joint_actualGradient_source (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (z w : CriticalPath μ) :
    ∃ G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 μ,
      (∀ᵐ t ∂μ, ∀ᵐ x ∂(volume : Measure Space), G t x =
        actualFullGradient alpha c ((jointFields μ z).u t) ((jointFields μ z).U t)
          ((jointFields μ z).V t) x - actualFullGradient alpha c ((jointFields μ w).u t)
          ((jointFields μ w).U t) ((jointFields μ w).V t) x) ∧
      ‖G‖ₑ = mixedNorm μ volume 2 (ENNReal.ofReal (6/5 : ℝ))
        (fun t => actualFullGradient alpha c ((jointFields μ z).u t) ((jointFields μ z).U t)
          ((jointFields μ z).V t) - actualFullGradient alpha c ((jointFields μ w).u t)
          ((jointFields μ w).U t) ((jointFields μ w).V t)) := by
  exact exists_actual_full_gradient_bochnerSource hH (T := T) μ
    (jointFields μ z).u (jointFields μ w).u
    (jointFields μ z).U (jointFields μ z).V (jointFields μ w).U (jointFields μ w).V
    (joint_slices μ hDensity hSob z w)
    (jointFields μ z).joint_u.aestronglyMeasurable (jointFields μ w).joint_u.aestronglyMeasurable
    (jointFields μ z).joint_U.aestronglyMeasurable (jointFields μ z).joint_V.aestronglyMeasurable
    (jointFields μ w).joint_U.aestronglyMeasurable (jointFields μ w).joint_V.aestronglyMeasurable
    (joint_actualGradient_finite μ hDensity hSob hH z w)

theorem exists_joint_actualGradient_source_withWeak (hDensity : OrdinaryH1Density) {K alpha c : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (z w : CriticalPath μ) :
    ∃ G : Lp (Lp (EuclideanSpace ℂ (Fin 3)) (ENNReal.ofReal (6/5 : ℝ))
      (volume : Measure Space)) 2 μ,
      (∀ᵐ t ∂μ, ∀ᵐ x ∂(volume : Measure Space), G t x =
        actualFullGradient alpha c ((jointFields μ z).u t) ((jointFields μ z).U t)
          ((jointFields μ z).V t) x - actualFullGradient alpha c ((jointFields μ w).u t)
          ((jointFields μ w).U t) ((jointFields μ w).V t) x) ∧
      (∀ᵐ t ∂μ,
        HasWeakGradient (fun x => (forcing alpha c ((jointFields μ z).u t) x -
          forcing alpha c ((jointFields μ w).u t) x).re) (fun x => gradientReal (G t x)) ∧
        HasWeakGradient (fun x => (forcing alpha c ((jointFields μ z).u t) x -
          forcing alpha c ((jointFields μ w).u t) x).im) (fun x => gradientImag (G t x))) := by
  let G := Classical.choose (exists_joint_actualGradient_source μ hDensity hSob hH z w)
  have hG := Classical.choose_spec (exists_joint_actualGradient_source μ hDensity hSob hH z w)
  refine ⟨G, hG.1, ?_⟩
  exact actual_gradient_bochnerSource_hasWeakGradients hDensity hSob hH (T := T) μ
    (jointFields μ z).u (jointFields μ w).u
    (jointFields μ z).U (jointFields μ z).V (jointFields μ w).U (jointFields μ w).V
    (joint_slices μ hDensity hSob z w) G hG.1

end HartreeF.CriticalJointSources
