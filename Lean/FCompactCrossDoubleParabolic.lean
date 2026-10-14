import FCompactCrossParabolic
import FCompactCrossSpatialScale

/-! The actual compact-box fields under the existing parabolic rescaling.
These quantitative bounds are uniform in arbitrary relative spatial/time centers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain TimeHolder CriticalAffine AffineMixed

theorem pure_cross_double_source_time {α c q r s : ℝ} (hHLS : OrdinaryHLS α c)
    (hq1 : 1 < q) (hqα : q < 3 / α) (hr : 0 < r)
    (hrel : 1 / r = 1 / q - α / 3) (hholder : Real.HolderTriple r s (6 / 5)) :
    ∃ C : ℝ≥0, ∀ (S T : Set Space) (I : Set ℝ),
      MeasurableSet S → MeasurableSet T → MeasurableSet I →
      volume S ≠ ∞ → volume T ≠ ∞ → volume I ≠ ∞ →
      ∀ (U H V K : ℝ), 0 ≤ U → 0 ≤ H → 0 ≤ V → 0 ≤ K →
      ∀ (u h v k : ℝ → Space → ℂ),
      Continuous (fun z : ℝ × Space => u z.1 z.2) →
      Continuous (fun z : ℝ × Space => h z.1 z.2) →
      Continuous (fun z : ℝ × Space => v z.1 z.2) →
      Continuous (fun z : ℝ × Space => k z.1 z.2) →
      (∀ t x, ‖u t x‖ ≤ U) → (∀ t x, ‖h t x‖ ≤ H) →
      (∀ t x, ‖v t x‖ ≤ V) → (∀ t x, ‖k t x‖ ≤ K) →
      (∀ t x, x ∉ S → u t x = 0) → (∀ t x, x ∉ T → v t x = 0) →
      (∀ t, t ∉ I → ∀ x, u t x = 0) →
      ∀ (a b : ℝ), 0 < a → 0 < b → ∀ (y z : Space) (d e : ℝ),
      forcingNorm (innerCross α c (parabolicField a y d (1/2) u)
        (parabolicField a y d (3/2) h) (parabolicField b z e (1/2) v)) ≠ ∞ ∧
      forcingNorm (outerCross α c (parabolicField a y d (1/2) u) (parabolicField b z e (1/2) v)
        (parabolicField b z e (3/2) k)) ≠ ∞ ∧
      forcingNorm (innerCross α c (parabolicField a y d (1/2) u)
        (parabolicField a y d (3/2) h) (parabolicField b z e (1/2) v)) ≤
        ENNReal.ofReal (a^((5+α)/2-3/q-1)) *
          (ENNReal.ofReal (b^((2+α)/2-3/s)) * supportBudget C q s S T I ((3+α)*U^(2+α)*H) (V^(2+α))) ∧
      forcingNorm (outerCross α c (parabolicField a y d (1/2) u) (parabolicField b z e (1/2) v)
        (parabolicField b z e (3/2) k)) ≤
        ENNReal.ofReal (a^((3+α)/2-3/q-1)) *
          (ENNReal.ofReal (b^((4+α)/2-3/s)) * supportBudget C q s S T I (U^(3+α)) ((2+α)*V^(1+α)*K)) := by
  obtain ⟨C,hC⟩ := pure_cross_source_scaled hHLS hq1 hqα hr hrel hholder
  refine ⟨C, fun S T I hS hT hI hSf hTf hIf U H V K hU hH hV hK u h v k hu hh hv hk
    huB hhB hvB hkB huS hvT huI a b ha hb y z d e => ?_⟩
  have hpreT : MeasurableSet ((affine b z) ⁻¹' T) := hT.preimage (by unfold affine; fun_prop)
  have hpreTf : volume ((affine b z) ⁻¹' T) ≠ ∞ := by
    rw [affine_preimage_volume hb z hT]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTf
  have hp := hC S ((affine b z) ⁻¹' T) I hS hpreT hI hSf hpreTf hIf
    U H (b^(1/2 : ℝ)*V) (b^(3/2 : ℝ)*K) hU hH (by positivity) (by positivity)
    u h (parabolicField b z e (1/2) v) (parabolicField b z e (3/2) k)
    hu hh (parabolicField_continuous z e (1/2) hv) (parabolicField_continuous z e (3/2) hk)
    huB hhB (parabolicField_amplitude hb z e (1/2) hvB) (parabolicField_amplitude hb z e (3/2) hkB)
    huS (parabolicField_space_support b z e (1/2) hvT) huI a ha y d
  have hi := hp.2.2.1
  have ho := hp.2.2.2
  rw [scaled_power hb hV, show (1/2:ℝ)*(2+α)=(2+α)/2 by ring,
    recipient_spaceBudget_scale hb hholder.symm.pos C q _ z I hT] at hi
  rw [scaled_power_product hb hV, show (1/2:ℝ)*(1+α)+3/2=(4+α)/2 by ring,
    recipient_spaceBudget_scale hb hholder.symm.pos C q _ z I hT] at ho
  exact ⟨hp.1,hp.2.1,hi,ho⟩

theorem pure_cross_double_recipient_time {α c q r s : ℝ} (hHLS : OrdinaryHLS α c)
    (hq1 : 1 < q) (hqα : q < 3 / α) (hr : 0 < r)
    (hrel : 1 / r = 1 / q - α / 3) (hholder : Real.HolderTriple r s (6 / 5)) :
    ∃ C : ℝ≥0, ∀ (S T : Set Space) (I : Set ℝ),
      MeasurableSet S → MeasurableSet T → MeasurableSet I →
      volume S ≠ ∞ → volume T ≠ ∞ → volume I ≠ ∞ →
      ∀ (U H V K : ℝ), 0 ≤ U → 0 ≤ H → 0 ≤ V → 0 ≤ K →
      ∀ (u h v k : ℝ → Space → ℂ),
      Continuous (fun z : ℝ × Space => u z.1 z.2) →
      Continuous (fun z : ℝ × Space => h z.1 z.2) →
      Continuous (fun z : ℝ × Space => v z.1 z.2) →
      Continuous (fun z : ℝ × Space => k z.1 z.2) →
      (∀ t x, ‖u t x‖ ≤ U) → (∀ t x, ‖h t x‖ ≤ H) →
      (∀ t x, ‖v t x‖ ≤ V) → (∀ t x, ‖k t x‖ ≤ K) →
      (∀ t x, x ∉ S → u t x = 0) → (∀ t x, x ∉ T → v t x = 0) →
      (∀ t, t ∉ I → ∀ x, v t x = 0) →
      ∀ (a b : ℝ), 0 < a → 0 < b → ∀ (y z : Space) (d e : ℝ),
      forcingNorm (innerCross α c (parabolicField b z e (1/2) u)
        (parabolicField b z e (3/2) h) (parabolicField a y d (1/2) v)) ≠ ∞ ∧
      forcingNorm (outerCross α c (parabolicField b z e (1/2) u) (parabolicField a y d (1/2) v)
        (parabolicField a y d (3/2) k)) ≠ ∞ ∧
      forcingNorm (innerCross α c (parabolicField b z e (1/2) u)
        (parabolicField b z e (3/2) h) (parabolicField a y d (1/2) v)) ≤
        ENNReal.ofReal (a^((2+α)/2-3/s-1)) *
          (ENNReal.ofReal (b^((5+α)/2-3/q)) * supportBudget C q s S T I ((3+α)*U^(2+α)*H) (V^(2+α))) ∧
      forcingNorm (outerCross α c (parabolicField b z e (1/2) u) (parabolicField a y d (1/2) v)
        (parabolicField a y d (3/2) k)) ≤
        ENNReal.ofReal (a^((4+α)/2-3/s-1)) *
          (ENNReal.ofReal (b^((3+α)/2-3/q)) * supportBudget C q s S T I (U^(3+α)) ((2+α)*V^(1+α)*K)) := by
  obtain ⟨C,hC⟩ := pure_cross_recipient_scaled hHLS hq1 hqα hr hrel hholder
  refine ⟨C, fun S T I hS hT hI hSf hTf hIf U H V K hU hH hV hK u h v k hu hh hv hk
    huB hhB hvB hkB huS hvT hvI a b ha hb y z d e => ?_⟩
  have hpreS : MeasurableSet ((affine b z) ⁻¹' S) := hS.preimage (by unfold affine; fun_prop)
  have hpreSf : volume ((affine b z) ⁻¹' S) ≠ ∞ := by
    rw [affine_preimage_volume hb z hS]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf
  have hp := hC ((affine b z) ⁻¹' S) T I hpreS hT hI hpreSf hTf hIf
    (b^(1/2 : ℝ)*U) (b^(3/2 : ℝ)*H) V K (by positivity) (by positivity) hV hK
    (parabolicField b z e (1/2) u) (parabolicField b z e (3/2) h) v k
    (parabolicField_continuous z e (1/2) hu) (parabolicField_continuous z e (3/2) hh) hv hk
    (parabolicField_amplitude hb z e (1/2) huB) (parabolicField_amplitude hb z e (3/2) hhB) hvB hkB
    (parabolicField_space_support b z e (1/2) huS) hvT hvI a ha y d
  have hi := hp.2.2.1
  have ho := hp.2.2.2
  rw [scaled_power_product hb hU, show (1/2:ℝ)*(2+α)+3/2=(5+α)/2 by ring,
    source_spaceBudget_scale hb (by linarith : 0 < q) C s _ z I hS] at hi
  rw [scaled_power hb hU, show (1/2:ℝ)*(3+α)=(3+α)/2 by ring,
    source_spaceBudget_scale hb (by linarith : 0 < q) C s _ z I hS] at ho
  exact ⟨hp.1,hp.2.1,hi,ho⟩

#print axioms pure_cross_double_source_time
#print axioms pure_cross_double_recipient_time
end HartreeF.CompactCross
