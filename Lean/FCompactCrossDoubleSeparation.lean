import FCompactCrossSeparationScale

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain CriticalAffine AffineMixed

/-- Actual two-scale off-diagonal bounds. The normalized support distance is
D*sqrt(a*b), with a,b the inverse physical scales. -/
theorem pure_cross_double_offDiagonal {α c a b D : ℝ} (hHLS : OrdinaryHLS α c)
    (ha : 0 < a) (hb : 0 < b) (hD : 0 < D) (y z : Space) (d e : ℝ)
    {S T : Set Space} {I J : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hI : MeasurableSet I) (hJ : MeasurableSet J)
    (hSf : volume S ≠ ∞) (hTf : volume T ≠ ∞) (hIf : volume I ≠ ∞) (hJf : volume J ≠ ∞)
    {U H V K : ℝ} (hU : 0 ≤ U) (hH : 0 ≤ H) (hV : 0 ≤ V) (hK : 0 ≤ K)
    {u h v k : ℝ → Space → ℂ}
    (hu : Continuous (fun q : ℝ × Space => u q.1 q.2))
    (hh : Continuous (fun q : ℝ × Space => h q.1 q.2))
    (hv : Continuous (fun q : ℝ × Space => v q.1 q.2))
    (hk : Continuous (fun q : ℝ × Space => k q.1 q.2))
    (huB : ∀ t x, ‖u t x‖ ≤ U) (hhB : ∀ t x, ‖h t x‖ ≤ H)
    (hvB : ∀ t x, ‖v t x‖ ≤ V) (hkB : ∀ t x, ‖k t x‖ ≤ K)
    (huS : ∀ t x, x ∉ S → u t x = 0) (hvT : ∀ t x, x ∉ T → v t x = 0)
    (huI : ∀ t, t ∉ I → ∀ x, u t x = 0) (hvJ : ∀ t, t ∉ J → ∀ x, v t x = 0)
    (hsep : ∀ x ∈ (affine b z) ⁻¹' T, ∀ w ∈ (affine a y) ⁻¹' S, D ≤ ‖x-w‖) :
    forcingNorm (innerCross α c (parabolicField a y d (1/2) u)
      (parabolicField a y d (3/2) h) (parabolicField b z e (1/2) v)) ≠ ∞ ∧
    forcingNorm (outerCross α c (parabolicField a y d (1/2) u)
      (parabolicField b z e (1/2) v) (parabolicField b z e (3/2) k)) ≠ ∞ ∧
    forcingNorm (innerCross α c (parabolicField a y d (1/2) u)
      (parabolicField a y d (3/2) h) (parabolicField b z e (1/2) v)) ≤
      ENNReal.ofReal ((D*Real.sqrt (a*b))^(α-3)) *
        separationBudget c ((3+α)*U^(2+α)*H) (V^(2+α)) S T I ∧
    forcingNorm (outerCross α c (parabolicField a y d (1/2) u)
      (parabolicField b z e (1/2) v) (parabolicField b z e (3/2) k)) ≤
      ENNReal.ofReal ((D*Real.sqrt (a*b))^(α-3)) *
        separationBudget c (U^(3+α)) ((2+α)*V^(1+α)*K) S T J := by
  have hpreS : MeasurableSet ((affine a y) ⁻¹' S) := hS.preimage (by unfold affine; fun_prop)
  have hpreT : MeasurableSet ((affine b z) ⁻¹' T) := hT.preimage (by unfold affine; fun_prop)
  have hpreI : MeasurableSet ((timeAffine a d) ⁻¹' I) := hI.preimage (by unfold timeAffine; fun_prop)
  have hpreJ : MeasurableSet ((timeAffine b e) ⁻¹' J) := hJ.preimage (by unfold timeAffine; fun_prop)
  have hpreSf : volume ((affine a y) ⁻¹' S) ≠ ∞ := by
    rw [affine_preimage_volume ha y hS]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf
  have hpreTf : volume ((affine b z) ⁻¹' T) ≠ ∞ := by
    rw [affine_preimage_volume hb z hT]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTf
  have hpreIf : volume ((timeAffine a d) ⁻¹' I) ≠ ∞ := by
    rw [timeAffine_preimage_volume ha d hI]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIf
  have hpreJf : volume ((timeAffine b e) ⁻¹' J) ≠ ∞ := by
    rw [timeAffine_preimage_volume hb e hJ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJf
  have hP (L : Set ℝ) (hL : MeasurableSet L) (hLf : volume L ≠ ∞)
      (hLt : ∀ t, t ∉ L → (∀ x, parabolicField a y d (1/2) u t x = 0) ∨
        (∀ x, parabolicField b z e (1/2) v t x = 0)) :=
    pure_cross_offDiagonal hHLS hD hpreS hpreT hL hpreSf hpreTf hLf
      (by positivity : 0 ≤ a^(1/2 : ℝ)*U) (by positivity : 0 ≤ a^(3/2 : ℝ)*H)
      (by positivity : 0 ≤ b^(1/2 : ℝ)*V) (by positivity : 0 ≤ b^(3/2 : ℝ)*K)
      (parabolicField_continuous y d (1/2) hu) (parabolicField_continuous y d (3/2) hh)
      (parabolicField_continuous z e (1/2) hv) (parabolicField_continuous z e (3/2) hk)
      (parabolicField_amplitude ha y d (1/2) huB) (parabolicField_amplitude ha y d (3/2) hhB)
      (parabolicField_amplitude hb z e (1/2) hvB) (parabolicField_amplitude hb z e (3/2) hkB)
      (parabolicField_space_support a y d (1/2) huS) (parabolicField_space_support b z e (1/2) hvT) hLt hsep
  have hpI := hP ((timeAffine a d) ⁻¹' I) hpreI hpreIf
    (fun t ht => Or.inl (parabolicField_time_support a y d (1/2) huI t ht))
  have hpJ := hP ((timeAffine b e) ⁻¹' J) hpreJ hpreJf
    (fun t ht => Or.inr (parabolicField_time_support b z e (1/2) hvJ t ht))
  have hi := hpI.2.2.1
  have ho := hpJ.2.2.2
  change _ ≤ separationBudget (c*D^(α-3))
    ((3+α)*(a^(1/2:ℝ)*U)^(2+α)*(a^(3/2:ℝ)*H)) ((b^(1/2:ℝ)*V)^(2+α))
    ((affine a y) ⁻¹' S) ((affine b z) ⁻¹' T) ((timeAffine a d) ⁻¹' I) at hi
  change _ ≤ separationBudget (c*D^(α-3))
    ((a^(1/2:ℝ)*U)^(3+α)) ((2+α)*(b^(1/2:ℝ)*V)^(1+α)*(b^(3/2:ℝ)*K))
    ((affine a y) ⁻¹' S) ((affine b z) ⁻¹' T) ((timeAffine b e) ⁻¹' J) at ho
  rw [scaled_power_product ha hU,scaled_power hb hV,
    show (1/2:ℝ)*(2+α)+3/2=(5+α)/2 by ring,show (1/2:ℝ)*(2+α)=(2+α)/2 by ring,
    separationBudget_scale ha hb ha _ _ y z d hS hT hI,
    mul_comm c (D^(α-3)),separationBudget_coeff (Real.rpow_nonneg hD.le _),←mul_assoc,
    ←ENNReal.ofReal_mul (by positivity),separated_inner_scale_identity ha hb hD] at hi
  rw [scaled_power ha hU,scaled_power_product hb hV,
    show (1/2:ℝ)*(3+α)=(3+α)/2 by ring,show (1/2:ℝ)*(1+α)+3/2=(4+α)/2 by ring,
    separationBudget_scale ha hb hb _ _ y z e hS hT hJ,
    mul_comm c (D^(α-3)),separationBudget_coeff (Real.rpow_nonneg hD.le _),←mul_assoc,
    ←ENNReal.ofReal_mul (by positivity),separated_outer_scale_identity ha hb hD] at ho
  exact ⟨hpI.1,hpI.2.1,hi,ho⟩

#print axioms pure_cross_double_offDiagonal
end HartreeF.CompactCross
