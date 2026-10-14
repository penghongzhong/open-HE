import HartreeGradientDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.GradientMajorants
open ForcingDomain

/-- The coefficient multiplying the critical difference-gradient norm. -/
def singleWeight (α : ℝ) (V Z : Space → ℝ) : ℝ :=
  spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (4 : ℝ) * spatialNorm (30/13) Z

/-- The coefficient multiplying the L10 difference norm. -/
def spacetimeDifferenceWeight (α : ℝ) (V W Y : Space → ℝ) : ℝ :=
  spatialNorm 6 V ^ (2*α) * spatialNorm 10 V ^ (3 : ℝ) *
    spatialNorm (30/13) Y * spatialNorm 10 W

/-- The exact mixed energy/spacetime difference coefficient. -/
def mixedDifferenceWeight (α : ℝ) (V W Y : Space → ℝ) : ℝ :=
  spatialNorm 6 V ^ (5*α/3) * spatialNorm 10 V ^ (4-theta α) *
    spatialNorm (30/13) Y * spatialNorm 6 W ^ (α/3) * spatialNorm 10 W ^ theta α

/-- The sum of the six literal gradient-difference majorants, in their paper order. -/
def majorantSum (α c : ℝ) (V W Y Z : Space → ℝ) : Space → ℝ :=
  majorant1 α c V Z + majorant2 α c V W Y + majorant3 α c V W Y +
    majorant4 α c V Z + majorant5 α c V W Y + majorant6 α c V W Y

/-- Every distinct defining Riesz integral in the six actual majorants is well-defined a.e. -/
structure MajorantDomains (α c : ℝ) (V W Y Z : Space → ℝ) : Prop where
  first : RieszDomain α c (fun x => V x ^ (3+α))
  second : RieszDomain α c (fun x => V x ^ (2+α) * W x)
  fourth : RieszDomain α c (fun x => V x ^ (2+α) * Z x)
  fifth : RieszDomain α c (fun x => V x ^ (1+α) * W x * Y x)
  sixth : RieszDomain α c (fun x => V x ^ (2+α) * Y x)

theorem singleWeight_nonneg (α : ℝ) (V Z : Space → ℝ) : 0 ≤ singleWeight α V Z := by
  unfold singleWeight
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (spatialNorm_nonneg _ _) _)
    (Real.rpow_nonneg (spatialNorm_nonneg _ _) _)) (spatialNorm_nonneg _ _)

theorem spacetimeDifferenceWeight_nonneg (α : ℝ) (V W Y : Space → ℝ) :
    0 ≤ spacetimeDifferenceWeight α V W Y := by
  unfold spacetimeDifferenceWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (spatialNorm_nonneg _ _) _)
    (Real.rpow_nonneg (spatialNorm_nonneg _ _) _)) (spatialNorm_nonneg _ _)) (spatialNorm_nonneg _ _)

theorem mixedDifferenceWeight_nonneg (α : ℝ) (V W Y : Space → ℝ) :
    0 ≤ mixedDifferenceWeight α V W Y := by
  unfold mixedDifferenceWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (Real.rpow_nonneg (spatialNorm_nonneg _ _) _) (Real.rpow_nonneg (spatialNorm_nonneg _ _) _))
    (spatialNorm_nonneg _ _)) (Real.rpow_nonneg (spatialNorm_nonneg _ _) _))
    (Real.rpow_nonneg (spatialNorm_nonneg _ _) _)

/-- The actual single-function gradient majorant T1+T4 is in L^(6/5).
The input derivative factor is an actual function in L^(30/13), with no L2 hypothesis. -/
theorem single_majorant_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V Z : Space → ℝ), (∀ x, 0 ≤ V x) →
      MemLp V 6 volume → MemLp V 10 volume →
      MemLp Z (ENNReal.ofReal (30/13 : ℝ)) volume →
      RieszDomain α c (fun x => V x ^ (3+α)) ∧
      RieszDomain α c (fun x => V x ^ (2+α) * Z x) ∧
      MemLp (majorant1 α c V Z + majorant4 α c V Z) (ENNReal.ofReal (6/5 : ℝ)) volume ∧
      spatialNorm (6/5) (majorant1 α c V Z + majorant4 α c V Z) ≤
        (C : ℝ) * singleWeight α V Z := by
  obtain ⟨C1,h1⟩ := majorant1_domain_bound hH
  obtain ⟨C4,h4⟩ := majorant4_domain_bound hH
  refine ⟨C1+C4, fun V Z hn h6 h10 hZ => ?_⟩
  obtain ⟨hd1,hb1⟩ := h1 V Z hn h6 h10 hZ
  obtain ⟨hd4,hb4⟩ := h4 V Z hn h6 h10 hZ
  have hb : SpatialBound (majorant1 α c V Z + majorant4 α c V Z) (5/6)
      (((C1+C4 : ℝ≥0) : ℝ)*singleWeight α V Z) := by
    convert hb1.add hb4 (by norm_num) using 1
    simp only [NNReal.coe_add, singleWeight]
    ring_nf
  exact ⟨hd1,hd4,hb.critical_result⟩

/-- Native fixed-space HLS/Holder bound for all six literal majorants.
This theorem supplies analytic operator estimates; the actual weak-gradient identity
and the subsequent time integration remain separate consumers. -/
theorem six_majorant_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ (V W Y Z : Space → ℝ), (∀ x, 0 ≤ V x) → (∀ x, 0 ≤ W x) →
      MemLp V 6 volume → MemLp V 10 volume → MemLp W 6 volume → MemLp W 10 volume →
      MemLp Y (ENNReal.ofReal (30/13 : ℝ)) volume →
      MemLp Z (ENNReal.ofReal (30/13 : ℝ)) volume →
      MajorantDomains α c V W Y Z ∧
      MemLp (majorantSum α c V W Y Z) (ENNReal.ofReal (6/5 : ℝ)) volume ∧
      spatialNorm (6/5) (majorantSum α c V W Y Z) ≤
        (C : ℝ) * (singleWeight α V Z + spacetimeDifferenceWeight α V W Y +
          mixedDifferenceWeight α V W Y) := by
  obtain ⟨C1,h1⟩ := majorant1_domain_bound hH
  obtain ⟨C2,h2⟩ := majorant2_domain_bound hH
  obtain ⟨C3,h3⟩ := majorant3_domain_bound hH
  obtain ⟨C4,h4⟩ := majorant4_domain_bound hH
  obtain ⟨C5,h5⟩ := majorant5_domain_bound hH
  obtain ⟨C6,h6⟩ := majorant6_domain_bound hH
  let C := C1+C2+C3+C4+C5+C6
  have hc14 : (C1 : ℝ)+(C4 : ℝ) ≤ (C : ℝ) := by
    dsimp [C]
    linarith [C2.coe_nonneg,C3.coe_nonneg,C5.coe_nonneg,C6.coe_nonneg]
  have hc35 : (C3 : ℝ)+(C5 : ℝ) ≤ (C : ℝ) := by
    dsimp [C]
    linarith [C1.coe_nonneg,C2.coe_nonneg,C4.coe_nonneg,C6.coe_nonneg]
  have hc26 : (C2 : ℝ)+(C6 : ℝ) ≤ (C : ℝ) := by
    dsimp [C]
    linarith [C1.coe_nonneg,C3.coe_nonneg,C4.coe_nonneg,C5.coe_nonneg]
  refine ⟨C, fun V W Y Z hnV hnW hV6 hV10 hW6 hW10 hY hZ => ?_⟩
  obtain ⟨hd1,hb1⟩ := h1 V Z hnV hV6 hV10 hZ
  obtain ⟨hd2,hb2⟩ := h2 V W Y hnV hnW hV6 hV10 hW6 hW10 hY
  obtain ⟨_,hb3⟩ := h3 V W Y hnV hV6 hV10 hW10 hY
  obtain ⟨hd4,hb4⟩ := h4 V Z hnV hV6 hV10 hZ
  obtain ⟨hd5,hb5⟩ := h5 V W Y hnV hV6 hV10 hW10 hY
  obtain ⟨hd6,hb6⟩ := h6 V W Y hnV hnW hV6 hV10 hW6 hW10 hY
  have h14 := hb1.add hb4 (by norm_num)
  have h35 := hb3.add hb5 (by norm_num)
  have h26 := hb2.add hb6 (by norm_num)
  have hb : SpatialBound (majorantSum α c V W Y Z) (5/6)
      (((C1 : ℝ)+(C4 : ℝ))*singleWeight α V Z +
        ((C3 : ℝ)+(C5 : ℝ))*spacetimeDifferenceWeight α V W Y +
        ((C2 : ℝ)+(C6 : ℝ))*mixedDifferenceWeight α V W Y) := by
    convert (h14.add h35 (by norm_num)).add h26 (by norm_num) using 1
    · ext x
      simp only [majorantSum, Pi.add_apply]
      ring_nf
    · unfold singleWeight spacetimeDifferenceWeight mixedDifferenceWeight
      ring_nf
  have hb' := hb.mono (show _ ≤ (C : ℝ)*(singleWeight α V Z +
      spacetimeDifferenceWeight α V W Y + mixedDifferenceWeight α V W Y) from
    (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_right hc14 (singleWeight_nonneg α V Z))
      (mul_le_mul_of_nonneg_right hc35 (spacetimeDifferenceWeight_nonneg α V W Y)))
      (mul_le_mul_of_nonneg_right hc26 (mixedDifferenceWeight_nonneg α V W Y))).trans_eq (by ring_nf))
  exact ⟨⟨hd1,hd2,hd4,hd5,hd6⟩,hb'.critical_result⟩

end HartreeF.GradientMajorants
