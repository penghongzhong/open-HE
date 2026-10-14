import FHartreeL2Spatial
import FTimeHolderCore
import FJointRieszMeasurability
import FJointLpRealization

/-! The literal L²_t L²_x source with exact E^(2α) S^5 time allocation.
Joint measurability and the iterated Bochner realization are proved here. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2
open ForcingDomain TimeHolder
local instance l2FiniteExponent : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

/-- Actual totalized convolution and local factor are jointly measurable. -/
theorem joint_forcing_measurable {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] (alpha c : ℝ) (u : T → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume)) :
    AEStronglyMeasurable (fun z : T × Space => forcing alpha c (u z.1) z.2)
      (mu.prod volume) := by
  have hp := joint_riesz_measurable mu alpha c (fun t x => ‖u t x‖ ^ (3 + alpha))
    (hu.norm.aemeasurable.pow_const (3 + alpha)).aestronglyMeasurable
  exact hp.smul ((hu.norm.aemeasurable.pow_const (1 + alpha)).aestronglyMeasurable.smul hu)

/-- Five spacetime powers consume exactly the time L² exponent. -/
theorem temporal_forcing_l2_holder {T : Type*} [MeasurableSpace T]
    (mu : Measure T) {alpha : ℝ} (ha : 0 < alpha) (E S : T → ℝ)
    (hE : AEStronglyMeasurable E mu) (hS : AEStronglyMeasurable S mu) :
    eLpNorm (fun t => ‖E t‖ ^ (2 * alpha) * ‖S t‖ ^ (5 : ℝ)) 2 mu ≤
      eLpNorm E ∞ mu ^ (2 * alpha) * eLpNorm S 10 mu ^ (5 : ℝ) := by
  have hEp := (hE.norm.aemeasurable.pow_const (2 * alpha)).aestronglyMeasurable
  have hSp := (hS.norm.aemeasurable.pow_const (5 : ℝ)).aestronglyMeasurable
  have hh := temporal_real_product_norm mu (p := ∞) (q := 2) (r := 2)
    (fun t => ‖E t‖ ^ (2 * alpha)) (fun t => ‖S t‖ ^ (5 : ℝ)) hEp hSp
  rw [temporal_native_infinity_power_norm mu (by positivity : 0 < 2 * alpha) E hE] at hh
  have hs : eLpNorm (fun t => ‖S t‖ ^ (5 : ℝ)) 2 mu = eLpNorm S 10 mu ^ (5 : ℝ) := by
    have hn := temporal_native_power_norm mu (by norm_num : (0 : ℝ) < 10)
      (by norm_num : (0 : ℝ) < 5) S hS
    norm_num [lpFromReciprocal] at hn ⊢
    exact hn
  rwa [hs] at hh

/-- The mixed norm is genuinely extended valued, so finite norms are never
inferred by taking toReal of infinity. The spatial domains are retained. -/
theorem forcing_l2_mixed_bound {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ {T : Type*} [MeasurableSpace T] (mu : Measure T) [SigmaFinite mu]
      (u : T → Space → ℂ),
      AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume) →
      (∀ᵐ t ∂mu, MemLp (u t) 6 volume ∧ MemLp (u t) 10 volume) →
      mixedNorm mu volume 2 2 (fun t => forcing alpha c (u t)) ≤
        (C : ℝ≥0∞) * mixedNorm mu volume ∞ 6 u ^ (2 * alpha) *
          mixedNorm mu volume 10 10 u ^ (5 : ℝ) := by
  obtain ⟨C, hC⟩ := forcing_l2_spatial_bound hH
  refine ⟨C, ?_⟩
  intro T _ mu _ u hu hs
  let E : T → ℝ := fun t => (eLpNorm (u t) 6 volume).toReal
  let S : T → ℝ := fun t => (eLpNorm (u t) 10 volume).toReal
  let a : T → ℝ≥0∞ := fun t => eLpNorm (forcing alpha c (u t)) 2 volume
  have hEm := spatial_lp_time_measurable mu volume 6 (by norm_num) (by norm_num) u hu
  have hSm := spatial_lp_time_measurable mu volume 10 (by norm_num) (by norm_num) u hu
  have hE : AEStronglyMeasurable E mu := hEm.aemeasurable.ennreal_toReal.aestronglyMeasurable
  have hS : AEStronglyMeasurable S mu := hSm.aemeasurable.ennreal_toReal.aestronglyMeasurable
  have ham : AEStronglyMeasurable a mu := spatial_lp_time_measurable mu volume 2
    (by norm_num) (by norm_num) _ (joint_forcing_measurable mu alpha c u hu)
  have haf : ∀ᵐ t ∂mu, a t ≠ ∞ := by
    filter_upwards [hs] with t ht
    exact (hC (u t) ht.1 ht.2).1.eLpNorm_ne_top
  have hmono : eLpNorm (fun t => (a t).toReal) 2 mu ≤
      eLpNorm ((C : ℝ) • (fun t => ‖E t‖ ^ (2 * alpha) * ‖S t‖ ^ (5 : ℝ))) 2 mu := by
    apply eLpNorm_mono_ae ham.aemeasurable.ennreal_toReal.aestronglyMeasurable
    filter_upwards [hs] with t ht
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    have hb := (hC (u t) ht.1 ht.2).2
    simpa only [E, S, Pi.smul_apply, smul_eq_mul,
      Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_assoc,
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ (C : ℝ) * ((eLpNorm (u t) 6 volume).toReal ^ (2 * alpha) *
          (eLpNorm (u t) 10 volume).toReal ^ (5 : ℝ)))] using hb
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal C.coe_nonneg, ENNReal.ofReal_coe_nnreal] at hmono
  have hb := hmono.trans (mul_le_mul' le_rfl (temporal_forcing_l2_holder mu hH.order_pos E S hE hS))
  have hEf : mixedNorm mu volume ∞ 6 u = eLpNorm E ∞ mu :=
    finite_extended_norm_bridge mu ∞ _ hEm (hs.mono fun _ ht => ht.1.eLpNorm_ne_top)
  have hSf : mixedNorm mu volume 10 10 u = eLpNorm S 10 mu :=
    finite_extended_norm_bridge mu 10 _ hSm (hs.mono fun _ ht => ht.2.eLpNorm_ne_top)
  change eLpNorm a 2 mu ≤ _
  rw [finite_extended_norm_bridge mu 2 a ham haf, hEf, hSf]
  simpa only [mul_assoc] using hb

/-- Source membership follows from exactly the two finite input norms. -/
theorem forcing_l2_mixed_finite {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : T → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hs : ∀ᵐ t ∂mu, MemLp (u t) 6 volume ∧ MemLp (u t) 10 volume)
    (hE : mixedNorm mu volume ∞ 6 u ≠ ∞) (hS : mixedNorm mu volume 10 10 u ≠ ∞) :
    mixedNorm mu volume 2 2 (fun t => forcing alpha c (u t)) ≠ ∞ := by
  obtain ⟨C, hC⟩ := forcing_l2_mixed_bound hH
  have ha : 0 ≤ 2 * alpha := by linarith [hH.order_pos]
  exact ne_top_of_le_ne_top (by finiteness) (hC mu u hu hs)

theorem forcing_l2_memLp {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    {u : Space → ℂ} (hu6 : MemLp u 6 volume) (hu10 : MemLp u 10 volume) :
    MemLp (forcing alpha c u) 2 volume := by
  obtain ⟨C, hC⟩ := forcing_l2_spatial_bound hH
  exact (hC u hu6 hu10).1

/-- A genuine iterated L² element for the literal Hartree forcing. -/
def l2Source {T : Type*} [MeasurableSpace T]
    (mu : Measure T) [SigmaFinite mu] {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    (u : T → Space → ℂ)
    (hu : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (mu.prod volume))
    (hs : ∀ᵐ t ∂mu, MemLp (u t) 6 volume ∧ MemLp (u t) 10 volume)
    (hE : mixedNorm mu volume ∞ 6 u ≠ ∞) (hS : mixedNorm mu volume 10 10 u ≠ ∞) :
    Lp (Lp ℂ 2 (volume : Measure Space)) 2 mu :=
  jointLpRealization mu volume 2 2
    (fun z : T × Space => forcing alpha c (u z.1) z.2)
    (joint_forcing_measurable mu alpha c u hu)
    (hs.mono fun t ht => forcing_l2_memLp (u := u t) hH ht.1 ht.2)
    (forcing_l2_mixed_finite mu hH u hu hs hE hS)

#print axioms joint_forcing_measurable
#print axioms temporal_forcing_l2_holder
#print axioms forcing_l2_mixed_bound
#print axioms forcing_l2_mixed_finite
#print axioms l2Source
end HartreeF.ForcingL2
