import FCompactCrossDoubleParabolic

/-! Uniform positive-power decay for the four literal pure cross terms.
The conclusion uses the existing parabolicField at two independent inverse scales a,b,
including derivative weight 3/2 and arbitrary relative centers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain TimeHolder CriticalAffine AffineMixed

/-- Four separate actual forcing norms, uniformly over translations and time centers.
This is derived from literal convolution estimates, not from assumed norm inequalities. -/
theorem box_pure_cross_ratio_decay {α c : ℝ} (hHLS : OrdinaryHLS α c)
    {S T : Set Space} {I : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hI : MeasurableSet I)
    (hSf : volume S ≠ ∞) (hTf : volume T ≠ ∞) (hIf : volume I ≠ ∞)
    {U H V K : ℝ} (hU : 0 ≤ U) (hH : 0 ≤ H) (hV : 0 ≤ V) (hK : 0 ≤ K)
    {u h v k : ℝ → Space → ℂ}
    (hu : Continuous (fun z : ℝ × Space => u z.1 z.2))
    (hh : Continuous (fun z : ℝ × Space => h z.1 z.2))
    (hv : Continuous (fun z : ℝ × Space => v z.1 z.2))
    (hk : Continuous (fun z : ℝ × Space => k z.1 z.2))
    (huB : ∀ t x, ‖u t x‖ ≤ U) (hhB : ∀ t x, ‖h t x‖ ≤ H)
    (hvB : ∀ t x, ‖v t x‖ ≤ V) (hkB : ∀ t x, ‖k t x‖ ≤ K)
    (huS : ∀ t x, x ∉ S → u t x = 0) (hvT : ∀ t x, x ∉ T → v t x = 0)
    (huI : ∀ t, t ∉ I → ∀ x, u t x = 0) :
    ∃ C : ℝ≥0, ∀ (a b : ℝ), 0 < a → 0 < b → b ≤ a → ∀ (y z : Space) (d e : ℝ),
      forcingNorm (innerCross α c (parabolicField a y d (1/2) u)
        (parabolicField a y d (3/2) h) (parabolicField b z e (1/2) v)) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((b/a)^((3-α)/4)) ∧
      forcingNorm (outerCross α c (parabolicField a y d (1/2) u) (parabolicField b z e (1/2) v)
        (parabolicField b z e (3/2) k)) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ((b/a)^((3-α)/4)) ∧
      forcingNorm (innerCross α c (parabolicField b z e (1/2) v)
        (parabolicField b z e (3/2) k) (parabolicField a y d (1/2) u)) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ((b/a)^((3-α)/4)) ∧
      forcingNorm (outerCross α c (parabolicField b z e (1/2) v) (parabolicField a y d (1/2) u)
        (parabolicField a y d (3/2) h)) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((b/a)^((3-α)/4)) := by
  have ha := hHLS.order_pos
  have ha3 := hHLS.order_lt_three
  obtain ⟨hqi,hqiα,hri,hreli,hholdi⟩ := inner_ranges ha ha3
  obtain ⟨hqo,hqoα,hro,hrelo,hholdo⟩ := outer_ranges ha ha3
  obtain ⟨Ci,hCi⟩ := pure_cross_double_source_time hHLS hqi hqiα hri hreli hholdi
  obtain ⟨Co,hCo⟩ := pure_cross_double_recipient_time hHLS hqo hqoα hro hrelo hholdo
  let B1 := supportBudget Ci (12/(9+α)) (12/(1+3*α)) S T I ((3+α)*U^(2+α)*H) (V^(2+α))
  let B2 := supportBudget Ci (12/(9+α)) (12/(1+3*α)) S T I (U^(3+α)) ((2+α)*V^(1+α)*K)
  let B3 := supportBudget Co (4/(1+α)) (12/(7+α)) T S I ((3+α)*V^(2+α)*K) (U^(2+α))
  let B4 := supportBudget Co (4/(1+α)) (12/(7+α)) T S I (V^(3+α)) ((2+α)*U^(1+α)*H)
  have hB1 : B1 ≠ ∞ := supportBudget_ne_top Ci (by positivity) (by positivity) hSf hTf hIf _ _
  have hB2 : B2 ≠ ∞ := supportBudget_ne_top Ci (by positivity) (by positivity) hSf hTf hIf _ _
  have hB3 : B3 ≠ ∞ := supportBudget_ne_top Co (by positivity) (by positivity) hTf hSf hIf _ _
  have hB4 : B4 ≠ ∞ := supportBudget_ne_top Co (by positivity) (by positivity) hTf hSf hIf _ _
  let D := max (max B1 B2) (max B3 B4)
  have hD : D ≠ ∞ := by dsimp [D]; finiteness
  let C : ℝ≥0 := D.toNNReal
  have hCD : (C : ℝ≥0∞) = D := ENNReal.coe_toNNReal hD
  refine ⟨C, fun a b haP hbP hba y z d e => ?_⟩
  have his := hCi S T I hS hT hI hSf hTf hIf U H V K hU hH hV hK u h v k hu hh hv hk
    huB hhB hvB hkB huS hvT huI a b haP hbP y z d e
  have hor := hCo T S I hT hS hI hTf hSf hIf V K U H hV hK hU hH v k u h hv hk hu hh
    hvB hkB huB hhB hvT huS huI a b haP hbP y z d e
  have hi1 : (5+α)/2-3/(12/(9+α))-1 = -((3-α)/4) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have hi2 : (3+α)/2-3/(12/(9+α))-1 = -((3-α)/4+1) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have ho1 : (2+α)/2-3/(12/(7+α))-1 = -((3-α)/4+1) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have ho2 : (4+α)/2-3/(12/(7+α))-1 = -((3-α)/4) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have hbi1 : (2+α)/2-3/(12/(1+3*α)) = (3-α)/4 := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have hbi2 : (4+α)/2-3/(12/(1+3*α)) = (3-α)/4+1 := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have hbo1 : (5+α)/2-3/(4/(1+α)) = (3-α)/4+1 := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have hbo2 : (3+α)/2-3/(4/(1+α)) = (3-α)/4 := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
  have hratio : b/a ≤ 1 := (div_le_iff₀ haP).mpr (by simpa using hba)
  have hgain : ENNReal.ofReal ((b/a)^((3-α)/4+1)) ≤ ENNReal.ofReal ((b/a)^((3-α)/4)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge (div_pos hbP haP) hratio (by linarith))
  have h1 := his.2.2.1
  have h2 := his.2.2.2
  have h3 := hor.2.2.1
  have h4 := hor.2.2.2
  rw [hi1,hbi1,←mul_assoc,two_scale_rpow haP hbP] at h1
  rw [hi2,hbi2,←mul_assoc,two_scale_rpow haP hbP] at h2
  rw [ho1,hbo1,←mul_assoc,two_scale_rpow haP hbP] at h3
  rw [ho2,hbo2,←mul_assoc,two_scale_rpow haP hbP] at h4
  have hb1 : B1 ≤ D := (le_max_left B1 B2).trans (le_max_left _ _)
  have hb2 : B2 ≤ D := (le_max_right B1 B2).trans (le_max_left _ _)
  have hb3 : B3 ≤ D := (le_max_left B3 B4).trans (le_max_right _ _)
  have hb4 : B4 ≤ D := (le_max_right B3 B4).trans (le_max_right _ _)
  simp only [hCD]
  refine ⟨?_,?_,?_,?_⟩
  · exact h1.trans (by simpa only [B1,mul_comm] using mul_le_mul' (le_refl (ENNReal.ofReal ((b/a)^((3-α)/4)))) hb1)
  · exact h2.trans (by simpa only [B2,mul_comm] using mul_le_mul' hgain hb2)
  · exact h3.trans (by simpa only [B3,mul_comm] using mul_le_mul' hgain hb3)
  · exact h4.trans (by simpa only [B4,mul_comm] using mul_le_mul' (le_refl (ENNReal.ofReal ((b/a)^((3-α)/4)))) hb4)

#print axioms box_pure_cross_ratio_decay
end HartreeF.CompactCross
