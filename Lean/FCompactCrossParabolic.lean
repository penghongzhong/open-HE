import FCompactCrossBudgets

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

theorem pure_cross_source_scaled {α c q r s : ℝ} (hHLS : OrdinaryHLS α c)
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
      ∀ (a : ℝ), 0 < a → ∀ (b : Space) (d : ℝ),
      forcingNorm (innerCross α c (parabolicField a b d (1/2) u)
        (parabolicField a b d (3/2) h) v) ≠ ∞ ∧
      forcingNorm (outerCross α c (parabolicField a b d (1/2) u) v k) ≠ ∞ ∧
      forcingNorm (innerCross α c (parabolicField a b d (1/2) u)
        (parabolicField a b d (3/2) h) v) ≤
        ENNReal.ofReal (a^((5+α)/2-3/q-1)) *
          supportBudget C q s S T I ((3+α)*U^(2+α)*H) (V^(2+α)) ∧
      forcingNorm (outerCross α c (parabolicField a b d (1/2) u) v k) ≤
        ENNReal.ofReal (a^((3+α)/2-3/q-1)) *
          supportBudget C q s S T I (U^(3+α)) ((2+α)*V^(1+α)*K) := by
  obtain ⟨C,hC⟩ := pure_cross_time_support_bound hHLS hq1 hqα hr hrel hholder
  refine ⟨C, fun S T I hS hT hI hSf hTf hIf U H V K hU hH hV hK u h v k hu hh hv hk
    huB hhB hvB hkB huS hvT huI a ha b d => ?_⟩
  have hpreS : MeasurableSet ((affine a b) ⁻¹' S) := hS.preimage (by unfold affine; fun_prop)
  have hpreI : MeasurableSet ((timeAffine a d) ⁻¹' I) := hI.preimage (by unfold timeAffine; fun_prop)
  have hpreSf : volume ((affine a b) ⁻¹' S) ≠ ∞ := by
    rw [affine_preimage_volume ha b hS]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf
  have hpreIf : volume ((timeAffine a d) ⁻¹' I) ≠ ∞ := by
    rw [timeAffine_preimage_volume ha d hI]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIf
  have hp := hC ((affine a b) ⁻¹' S) T ((timeAffine a d) ⁻¹' I)
    hpreS hT hpreI hpreSf hTf hpreIf (a^(1/2 : ℝ)*U) (a^(3/2 : ℝ)*H) V K
    (by positivity) (by positivity) hV hK
    (parabolicField a b d (1/2) u) (parabolicField a b d (3/2) h) v k
    (parabolicField_continuous b d (1/2) hu) (parabolicField_continuous b d (3/2) hh) hv hk
    (parabolicField_amplitude ha b d (1/2) huB) (parabolicField_amplitude ha b d (3/2) hhB) hvB hkB
    (parabolicField_space_support a b d (1/2) huS) hvT
    (fun t ht => Or.inl (parabolicField_time_support a b d (1/2) huI t ht))
  have hi := hp.2.2.1
  have ho := hp.2.2.2
  change _ ≤ supportBudget C q s ((affine a b) ⁻¹' S) T ((timeAffine a d) ⁻¹' I)
    ((3+α)*(a^(1/2 : ℝ)*U)^(2+α)*(a^(3/2 : ℝ)*H)) (V^(2+α)) at hi
  change _ ≤ supportBudget C q s ((affine a b) ⁻¹' S) T ((timeAffine a d) ⁻¹' I)
    ((a^(1/2 : ℝ)*U)^(3+α)) ((2+α)*V^(1+α)*K) at ho
  rw [scaled_power_product ha hU, show (1/2:ℝ)*(2+α)+3/2=(5+α)/2 by ring,
    source_supportBudget_scale ha (by linarith : 0 < q) C s _ b d hS hI] at hi
  rw [scaled_power ha hU, show (1/2:ℝ)*(3+α)=(3+α)/2 by ring,
    source_supportBudget_scale ha (by linarith : 0 < q) C s _ b d hS hI] at ho
  exact ⟨hp.1,hp.2.1,hi,ho⟩

theorem pure_cross_recipient_scaled {α c q r s : ℝ} (hHLS : OrdinaryHLS α c)
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
      ∀ (a : ℝ), 0 < a → ∀ (b : Space) (d : ℝ),
      forcingNorm (innerCross α c u h (parabolicField a b d (1/2) v)) ≠ ∞ ∧
      forcingNorm (outerCross α c u (parabolicField a b d (1/2) v)
        (parabolicField a b d (3/2) k)) ≠ ∞ ∧
      forcingNorm (innerCross α c u h (parabolicField a b d (1/2) v)) ≤
        ENNReal.ofReal (a^((2+α)/2-3/s-1)) *
          supportBudget C q s S T I ((3+α)*U^(2+α)*H) (V^(2+α)) ∧
      forcingNorm (outerCross α c u (parabolicField a b d (1/2) v)
        (parabolicField a b d (3/2) k)) ≤
        ENNReal.ofReal (a^((4+α)/2-3/s-1)) *
          supportBudget C q s S T I (U^(3+α)) ((2+α)*V^(1+α)*K) := by
  obtain ⟨C,hC⟩ := pure_cross_time_support_bound hHLS hq1 hqα hr hrel hholder
  refine ⟨C, fun S T I hS hT hI hSf hTf hIf U H V K hU hH hV hK u h v k hu hh hv hk
    huB hhB hvB hkB huS hvT hvI a ha b d => ?_⟩
  have hpreT : MeasurableSet ((affine a b) ⁻¹' T) := hT.preimage (by unfold affine; fun_prop)
  have hpreI : MeasurableSet ((timeAffine a d) ⁻¹' I) := hI.preimage (by unfold timeAffine; fun_prop)
  have hpreTf : volume ((affine a b) ⁻¹' T) ≠ ∞ := by
    rw [affine_preimage_volume ha b hT]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTf
  have hpreIf : volume ((timeAffine a d) ⁻¹' I) ≠ ∞ := by
    rw [timeAffine_preimage_volume ha d hI]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIf
  have hp := hC S ((affine a b) ⁻¹' T) ((timeAffine a d) ⁻¹' I)
    hS hpreT hpreI hSf hpreTf hpreIf U H (a^(1/2 : ℝ)*V) (a^(3/2 : ℝ)*K)
    hU hH (by positivity) (by positivity)
    u h (parabolicField a b d (1/2) v) (parabolicField a b d (3/2) k)
    hu hh (parabolicField_continuous b d (1/2) hv) (parabolicField_continuous b d (3/2) hk)
    huB hhB (parabolicField_amplitude ha b d (1/2) hvB) (parabolicField_amplitude ha b d (3/2) hkB)
    huS (parabolicField_space_support a b d (1/2) hvT)
    (fun t ht => Or.inr (parabolicField_time_support a b d (1/2) hvI t ht))
  have hi := hp.2.2.1
  have ho := hp.2.2.2
  change _ ≤ supportBudget C q s S ((affine a b) ⁻¹' T) ((timeAffine a d) ⁻¹' I)
    ((3+α)*U^(2+α)*H) ((a^(1/2 : ℝ)*V)^(2+α)) at hi
  change _ ≤ supportBudget C q s S ((affine a b) ⁻¹' T) ((timeAffine a d) ⁻¹' I)
    (U^(3+α)) ((2+α)*(a^(1/2 : ℝ)*V)^(1+α)*(a^(3/2 : ℝ)*K)) at ho
  rw [scaled_power ha hV, show (1/2:ℝ)*(2+α)=(2+α)/2 by ring,
    recipient_supportBudget_scale ha hholder.symm.pos C q _ b d hT hI] at hi
  rw [scaled_power_product ha hV, show (1/2:ℝ)*(1+α)+3/2=(4+α)/2 by ring,
    recipient_supportBudget_scale ha hholder.symm.pos C q _ b d hT hI] at ho
  exact ⟨hp.1,hp.2.1,hi,ho⟩

#print axioms pure_cross_source_scaled
#print axioms pure_cross_recipient_scaled
end HartreeF.CompactCross
