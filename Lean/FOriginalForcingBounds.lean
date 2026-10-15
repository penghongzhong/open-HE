import HartreeForcingDomain

/-!
Original v23 Lemma 2.21: the two actual forcing domains and exponents,
with one finite constant chosen before the input function. The identification
of this constant with the manuscript's optimal bilinear HLS constant is a
separate obligation; this module does not claim full acceptance of Lemma 2.21.
-/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.OriginalForcingBounds
open ForcingDomain

/-- Exactly two L4 factors and alpha L6 factors, including zero-valued inputs. -/
theorem localFactor_four_six {alpha : ℝ} (ha : 0 < alpha)
    {f : Space → ℂ} (h4 : MemLp f 4 volume) (h6 : MemLp f 6 volume) :
    MemLp (localFactor alpha f) (ENNReal.ofReal (densityExponent alpha)) volume ∧
      eLpNorm (localFactor alpha f) (ENNReal.ofReal (densityExponent alpha)) volume ≤
        eLpNorm f 4 volume ^ (2 : ℝ) * eLpNorm f 6 volume ^ alpha := by
  let a : Space → ℝ := fun x => ‖f x‖ ^ (2 : ℝ)
  let b : Space → ℝ := fun x => ‖f x‖ ^ alpha
  have ha2 : MemLp a 2 volume := by
    simpa [a, show (4 : ℝ) / 2 = 2 by norm_num] using norm_power_memLp (p := 4) (s := 2) (by norm_num)
      (by simpa using h4)
  have hb : MemLp b (ENNReal.ofReal (6 / alpha)) volume :=
    norm_power_memLp ha (by simpa using h6)
  have ht : Real.HolderTriple 2 (6 / alpha) (densityExponent alpha) := by
    constructor
    · simp only [densityExponent, inv_div]
      ring
    · norm_num
    · exact div_pos (by norm_num) ha
  let : ENNReal.HolderTriple 2 (ENNReal.ofReal (6 / alpha))
      (ENNReal.ofReal (densityExponent alpha)) := by
    simpa only [ENNReal.ofReal_ofNat] using ht.ennrealOfReal
  have hab : MemLp (a * b) (ENNReal.ofReal (densityExponent alpha)) volume := ha2.mul hb
  have he : ∀ x, ‖localFactor alpha f x‖ = ‖(a * b) x‖ := by
    intro x
    rw [norm_localFactor ha]
    change ‖f x‖ ^ (2 + alpha) = |‖f x‖ ^ (2 : ℝ) * ‖f x‖ ^ alpha|
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _))]
    exact Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) ha.le
  have hm := localFactor_measurable alpha h6.aestronglyMeasurable
  refine ⟨hab.of_le hm (Filter.Eventually.of_forall fun x => (he x).le), ?_⟩
  rw [eLpNorm_congr_norm_ae hm hab.aestronglyMeasurable (Filter.Eventually.of_forall he)]
  have hh : eLpNorm (a * b) (ENNReal.ofReal (densityExponent alpha)) volume ≤
      eLpNorm a 2 volume * eLpNorm b (ENNReal.ofReal (6 / alpha)) volume :=
    eLpNorm_smul_le_mul_eLpNorm ha2.aestronglyMeasurable hb.aestronglyMeasurable
  have hna : eLpNorm a 2 volume = eLpNorm f 4 volume ^ (2 : ℝ) := by
    simpa [a, show (4 : ℝ) / 2 = 2 by norm_num] using norm_power_eLpNorm (p := 4) (s := 2) (by norm_num)
      h4.aestronglyMeasurable
  have hnb : eLpNorm b (ENNReal.ofReal (6 / alpha)) volume =
      eLpNorm f 6 volume ^ alpha := by
    simpa only [b, ENNReal.ofReal_ofNat] using
      norm_power_eLpNorm (p := 6) ha h6.aestronglyMeasurable
  rwa [hna, hnb] at hh

/-- The two paper exponents, with one uniform finite constant and genuine
memberships before real norms. No mass, gradient, radiality, or trajectory
assumption is needed. The optimal-constant identification is not asserted. -/
theorem exists_common_forcing_bounds {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ f : Space → ℂ, MemLp f 6 volume →
      MemLp (forcing alpha c f) (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
      (eLpNorm (forcing alpha c f) (ENNReal.ofReal (6 / 5 : ℝ)) volume).toReal ≤
        (C : ℝ) * (eLpNorm f 6 volume).toReal ^ (5 + 2 * alpha) ∧
      (MemLp f 4 volume → Integrable (forcing alpha c f) volume ∧
        (eLpNorm (forcing alpha c f) 1 volume).toReal ≤
          (C : ℝ) * (eLpNorm f 4 volume).toReal ^ (2 : ℝ) *
            (eLpNorm f 6 volume).toReal ^ (3 + 2 * alpha)) := by
  have ha : 0 < alpha := hH.order_pos
  obtain ⟨C, hC⟩ := potential_domain_bound hH
  refine ⟨C, fun f h6 => ?_⟩
  obtain ⟨_, hp, hb⟩ := hC f h6
  have hl : MemLp (localFactor alpha f) (ENNReal.ofReal (energyOuterExponent alpha)) volume :=
    localFactor_memLp hH.order_pos (by simpa using h6)
  let := (energy_holder hH.order_pos hH.order_lt_three).ennrealOfReal
  have hmem : MemLp (forcing alpha c f) (ENNReal.ofReal (6 / 5 : ℝ)) volume := hp.smul hl
  have henergy : eLpNorm (forcing alpha c f) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + alpha) * eLpNorm f 6 volume ^ (2 + alpha) := by
    calc
      _ ≤ eLpNorm (potential alpha c f) (ENNReal.ofReal (potentialExponent alpha)) volume *
          eLpNorm (localFactor alpha f) (ENNReal.ofReal (energyOuterExponent alpha)) volume :=
        eLpNorm_smul_le_mul_eLpNorm hp.aestronglyMeasurable hl.aestronglyMeasurable
      _ = eLpNorm (potential alpha c f) (ENNReal.ofReal (potentialExponent alpha)) volume *
          eLpNorm f 6 volume ^ (2 + alpha) := by
        congr 1
        simpa only [energyOuterExponent, ENNReal.ofReal_ofNat] using
          localFactor_eLpNorm (p := 6) hH.order_pos h6.aestronglyMeasurable
      _ ≤ _ := by gcongr
  have hfinite : (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + alpha) *
      eLpNorm f 6 volume ^ (2 + alpha) ≠ ∞ := by
    finiteness [h6.eLpNorm_ne_top]
  have her := ENNReal.toReal_mono hfinite henergy
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow] at her
  refine ⟨hmem, ?_, fun h4 => ?_⟩
  · have he : (eLpNorm f 6 volume).toReal ^ (5 + 2 * alpha) =
        (eLpNorm f 6 volume).toReal ^ (3 + alpha) *
          (eLpNorm f 6 volume).toReal ^ (2 + alpha) := by
      rw [show (5 : ℝ) + 2 * alpha = (3 + alpha) + (2 + alpha) by ring]
      exact Real.rpow_add_of_nonneg ENNReal.toReal_nonneg
        (by linarith [hH.order_pos]) (by linarith [hH.order_pos])
    simpa only [he, mul_assoc] using her
  · obtain ⟨hm4, hbound4⟩ := localFactor_four_six ha h4 h6
    let : ENNReal.HolderTriple (ENNReal.ofReal (potentialExponent alpha))
        (ENNReal.ofReal (densityExponent alpha)) 1 := by
      simpa only [ENNReal.ofReal_one] using
        (critical_holder hH.order_pos hH.order_lt_three).ennrealOfReal
    have hmem1 : MemLp (forcing alpha c f) 1 volume := hp.smul hm4
    have hbound1 : eLpNorm (forcing alpha c f) 1 volume ≤
        (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + alpha) *
          (eLpNorm f 4 volume ^ (2 : ℝ) * eLpNorm f 6 volume ^ alpha) := by
      have hh := eLpNorm_smul_le_mul_eLpNorm (r := 1)
        hp.aestronglyMeasurable hm4.aestronglyMeasurable
      exact hh.trans (mul_le_mul' hb hbound4)
    have hfin1 : (C : ℝ≥0∞) * eLpNorm f 6 volume ^ (3 + alpha) *
        (eLpNorm f 4 volume ^ (2 : ℝ) * eLpNorm f 6 volume ^ alpha) ≠ ∞ := by
      finiteness [h4.eLpNorm_ne_top, h6.eLpNorm_ne_top]
    have hr := ENNReal.toReal_mono hfin1 hbound1
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow] at hr
    refine ⟨memLp_one_iff_integrable.mp hmem1, hr.trans_eq ?_⟩
    have he : (eLpNorm f 6 volume).toReal ^ (3 + 2 * alpha) =
        (eLpNorm f 6 volume).toReal ^ (3 + alpha) *
          (eLpNorm f 6 volume).toReal ^ alpha := by
      rw [show (3 : ℝ) + 2 * alpha = (3 + alpha) + alpha by ring]
      exact Real.rpow_add_of_nonneg ENNReal.toReal_nonneg
        (by linarith [hH.order_pos]) hH.order_pos.le
    rw [he]
    ring

#print axioms localFactor_four_six
#print axioms exists_common_forcing_bounds
end HartreeF.OriginalForcingBounds
