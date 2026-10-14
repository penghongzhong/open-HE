import FFiniteProfileRieszMixed
import FCompactCrossTerms

/-! The two new Q-weighted coefficient rows. Author source, UNCOMPILED.
The actual direction has no W assumption. Pure rows use the zero-direction
ScalarProfile, and the a = 0 factor is omitted by weighted_pair_le itself. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HartreeF.FreeValueFullCandidate
open TimeHolder ForcingDomain WeakHartreeChain DerivativeMajorization
  CompactCross GeneralProfileCross ProfileApproximation LocalProfileProducts
  FiniteProfileMixedDefects FiniteProfileRieszMixed

/-- The genuine overlap Q = L5_t L(15/8)_x of |u||h|. -/
def Q (u h : ℝ → Space → ℂ) : ℝ≥0∞ :=
  localProductNorm (ENNReal.ofReal (15/8 : ℝ)) u h

/-- Pure value estimates require no domain of the unrelated direction. -/
theorem zero_direction_profile (u : ℝ → Space → ℂ)
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hE : mixedNorm volume volume ∞ 6 u ≠ ∞)
    (hS : mixedNorm volume volume 10 10 u ≠ ∞) :
    ScalarProfile u (0 : ℝ → Space → ℂ) := by
  exact ⟨hu, stronglyMeasurable_const, hE, hS, by simp [mixedNorm]⟩

/-- The genuine weighted_pair_le specialization at overlap reciprocals
(1/5,8/15), d = 1. In particular a = 0 does not introduce 1 into Lp. -/
theorem power_VSQ_le {u h : ℝ → Space → ℂ}
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hh : StronglyMeasurable (fun z : ℝ × Space => h z.1 z.2))
    (hE : mixedNorm volume volume ∞ 6 u ≠ ∞)
    (hS : mixedNorm volume volume 10 10 u ≠ ∞) (hQ : Q u h ≠ ∞)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    mixedNorm volume volume (reciprocal (b/10+1/5))
      (reciprocal (a/6+b/10+8/15))
      (fun t x => ‖u t x‖ ^ (a+b+1) * ‖h t x‖) ≤
      mixedNorm volume volume ∞ 6 u ^ a * mixedNorm volume volume 10 10 u ^ b * Q u h := by
  let R : ℝ → Space → ℝ := fun t x => ‖u t x‖
  let P : ℝ → Space → ℝ := normProduct u h
  have hR : AEStronglyMeasurable (fun z : ℝ × Space => R z.1 z.2)
      (volume.prod volume) := hu.aestronglyMeasurable.norm
  have hP : AEStronglyMeasurable (fun z : ℝ × Space => P z.1 z.2)
      (volume.prod volume) := hu.aestronglyMeasurable.norm.mul hh.aestronglyMeasurable.norm
  have hReq (p q : ℝ≥0∞) : mixedNorm volume volume p q R = mixedNorm volume volume p q u :=
    mixed_norm_norm_eq volume p q u hu.aestronglyMeasurable
  have hR6 : mixedNorm volume volume ∞ 6 R ≠ ∞ := by rw [hReq]; exact hE
  have hR10 : mixedNorm volume volume 10 10 R ≠ ∞ := by rw [hReq]; exact hS
  have ht : reciprocal (1/5 : ℝ) = 5 := by norm_num [reciprocal]
  have hx : reciprocal (8/15 : ℝ) = ENNReal.ofReal (15/8 : ℝ) := by norm_num [reciprocal]
  have hPf : mixedNorm volume volume (reciprocal (1/5)) (reciprocal (8/15)) P ≠ ∞ := by
    simpa only [ht, hx, P, Q, localProductNorm] using hQ
  have hw := weighted_pair_le ha hb (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1/5) (by norm_num : (0 : ℝ) < 8/15)
    R P hR hP hR6 hR10 hPf
  have he : (fun t x => ‖R t x‖ ^ a * ‖R t x‖ ^ b * ‖P t x‖ ^ (1 : ℝ)) =
      (fun t x => ‖u t x‖ ^ (a+b+1) * ‖h t x‖) := by
    funext t x
    simp only [R, P, normProduct, norm_norm,
      Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), Real.rpow_one]
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) ha hb, ← mul_assoc,
      ← Real.rpow_add_one' (norm_nonneg _) (by linarith : a+b+1 ≠ 0)]
  rw [he] at hw
  simpa only [hReq, ht, hx, Q, localProductNorm, P, ENNReal.rpow_one, mul_one] using hw

/-- Measurability of all four actual signed/complex coefficients. -/
theorem q_coefficients_joint {α : ℝ} (hα : 0 < α) {u h : ℝ → Space → ℂ}
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hh : StronglyMeasurable (fun z : ℝ × Space => h z.1 z.2)) :
    AEStronglyMeasurable (fun z : ℝ × Space => pureDensity α u z.1 z.2) (volume.prod volume) ∧
    AEStronglyMeasurable (fun z : ℝ × Space => pureDensityDerivative α u h z.1 z.2) (volume.prod volume) ∧
    AEStronglyMeasurable (fun z : ℝ × Space => pureLocal α u z.1 z.2) (volume.prod volume) ∧
    AEStronglyMeasurable (fun z : ℝ × Space => pureLocalDerivative α u h z.1 z.2) (volume.prod volume) := by
  exact ⟨((density_contDiff_one (by linarith : 1 < 3+α)).continuous.comp_stronglyMeasurable hu).aestronglyMeasurable,
    density_action_measurable (volume.prod volume) (3+α) hu.aestronglyMeasurable hh.aestronglyMeasurable,
    ((localFactor_contDiff_one (by linarith : 1 < 1+α)).continuous.comp_stronglyMeasurable hu).aestronglyMeasurable,
    local_factor_action_measurable (volume.prod volume) (1+α) hu.aestronglyMeasurable hh.aestronglyMeasurable⟩

/-- E/S/Q control of the full coefficient ledger; no W(h) hypothesis occurs. -/
theorem q_coefficients_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u h : ℝ → Space → ℂ}
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hh : StronglyMeasurable (fun z : ℝ × Space => h z.1 z.2))
    (hE : mixedNorm volume volume ∞ 6 u ≠ ∞)
    (hS : mixedNorm volume volume 10 10 u ≠ ∞) (hQ : Q u h ≠ ∞) :
    mixedNorm volume volume (t0 α) (x0 α) (pureDensity α u) ≤
      mixedNorm volume volume ∞ 6 u ^ (2*α) * mixedNorm volume volume 10 10 u ^ (3-α) ∧
    mixedNorm volume volume (t1 α) (x1 α) (pureDensityDerivative α u h) ≤
      ENNReal.ofReal (3+α) * (mixedNorm volume volume ∞ 6 u ^ (α/3) *
        mixedNorm volume volume 10 10 u ^ (1+2*α/3) * Q u h) ∧
    mixedNorm volume volume (t2 α) (x2 α) (pureLocal α u) ≤
      mixedNorm volume volume ∞ 6 u ^ (5*α/3) * mixedNorm volume volume 10 10 u ^ (2-2*α/3) ∧
    mixedNorm volume volume (t3 α) (x3 α) (pureLocalDerivative α u h) ≤
      ENNReal.ofReal (2+α) * (mixedNorm volume volume 10 10 u ^ α * Q u h) := by
  have hpure := pure_coefficients_bound hα hα3 (zero_direction_profile u hu hE hS)
  have hm := q_coefficients_joint hα hu hh
  have hd := ledger_domains hα hα3
  refine ⟨hpure.1, ?_, hpure.2.2.1, ?_⟩
  · let B : ℝ → Space → ℝ := fun t x => ‖u t x‖^(2+α)*‖h t x‖
    have hdom (t : ℝ) (x : Space) : ‖pureDensityDerivative α u h t x‖ ≤ (3+α)*‖B t x‖ := by
      have h := (densityDerivative (3+α) (u t x)).le_opNorm (h t x)
      rw [densityDerivative_norm (by linarith : 1 < 3+α)] at h
      simpa only [pureDensityDerivative, B, show (3+α)-1=2+α by ring,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)), mul_assoc] using h
    have hb : mixedNorm volume volume (t1 α) (x1 α) B ≤
        mixedNorm volume volume ∞ 6 u ^ (α/3) *
          mixedNorm volume volume 10 10 u ^ (1+2*α/3) * Q u h := by
      simpa only [B, t1, x1, show α/3+(1+2*α/3)+1=2+α by ring,
        show (1+2*α/3)/10+1/5=(3+2*α/3)/10 by ring,
        show (α/3)/6+(1+2*α/3)/10+8/15=(57+11*α)/90 by ring] using
        power_VSQ_le hu hh hE hS hQ (show 0 ≤ α/3 by positivity)
          (show 0 ≤ 1+2*α/3 by positivity)
    exact (mixed_le_const_mul (reciprocal_ne_zero _) hd.2.1.2.2
      (by linarith : 0 ≤ 3+α) _ B hm.2.1 hdom).trans (mul_le_mul' le_rfl hb)
  · let B : ℝ → Space → ℝ := fun t x => ‖u t x‖^(1+α)*‖h t x‖
    have hdom (t : ℝ) (x : Space) : ‖pureLocalDerivative α u h t x‖ ≤ (2+α)*‖B t x‖ := by
      have hder := (localFactorDerivative (1+α) (u t x)).le_opNorm (h t x)
      have hb := mul_le_mul_of_nonneg_right
        (localFactorDerivative_bound (by linarith : 1 < 1+α) (u t x)) (norm_nonneg (h t x))
      simpa only [pureLocalDerivative, B, show (1+α)+1=2+α by ring,
        Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _)), mul_assoc] using hder.trans hb
    have hb : mixedNorm volume volume (t3 α) (x3 α) B ≤
        mixedNorm volume volume 10 10 u ^ α * Q u h := by
      simpa only [B, t3, x3, zero_add, zero_div, ENNReal.rpow_zero, one_mul,
        show α+1=1+α by ring, show α/10+1/5=(2+α)/10 by ring,
        show α/10+8/15=(16+3*α)/30 by ring] using
        power_VSQ_le hu hh hE hS hQ (by norm_num : (0 : ℝ) ≤ 0) hα.le
    exact (mixed_le_const_mul (reciprocal_ne_zero _) hd.2.2.2.2.2
      (by linarith : 0 ≤ 2+α) _ B hm.2.2.2 hdom).trans (mul_le_mul' le_rfl hb)

/-- True every-input finiteness of each coefficient, before invoking HLS. -/
theorem q_coefficients_finite {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u h : ℝ → Space → ℂ}
    (hu : StronglyMeasurable (fun z : ℝ × Space => u z.1 z.2))
    (hh : StronglyMeasurable (fun z : ℝ × Space => h z.1 z.2))
    (hE : mixedNorm volume volume ∞ 6 u ≠ ∞)
    (hS : mixedNorm volume volume 10 10 u ≠ ∞) (hQ : Q u h ≠ ∞) :
    mixedNorm volume volume (t0 α) (x0 α) (pureDensity α u) ≠ ∞ ∧
    mixedNorm volume volume (t1 α) (x1 α) (pureDensityDerivative α u h) ≠ ∞ ∧
    mixedNorm volume volume (t2 α) (x2 α) (pureLocal α u) ≠ ∞ ∧
    mixedNorm volume volume (t3 α) (x3 α) (pureLocalDerivative α u h) ≠ ∞ := by
  have ha0 : 0 ≤ 2*α := by positivity
  have hb0 : 0 ≤ 3-α := by linarith
  have ha1 : 0 ≤ α/3 := by positivity
  have hb1 : 0 ≤ 1+2*α/3 := by positivity
  have ha2 : 0 ≤ 5*α/3 := by positivity
  have hb2 : 0 ≤ 2-2*α/3 := by linarith
  have hb3 : 0 ≤ α := hα.le
  obtain ⟨h0,h1,h2,h3⟩ := q_coefficients_bound hα hα3 hu hh hE hS hQ
  exact ⟨ne_top_of_le_ne_top (by finiteness) h0,
    ne_top_of_le_ne_top (by finiteness) h1,
    ne_top_of_le_ne_top (by finiteness) h2,
    ne_top_of_le_ne_top (by finiteness) h3⟩

/-- The actual finite value sum has the finite Q envelope, including the empty sum. -/
theorem Q_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℝ → Space → ℂ)
    (h : ℝ → Space → ℂ)
    (hu : ∀ i ∈ s, AEStronglyMeasurable (fun z : ℝ × Space => u i z.1 z.2) (volume.prod volume))
    (hh : AEStronglyMeasurable (fun z : ℝ × Space => h z.1 z.2) (volume.prod volume)) :
    Q (fun t x => ∑ i ∈ s, u i t x) h ≤ ∑ i ∈ s, Q (u i) h := by
  classical
  have hsum := Finset.aestronglyMeasurable_fun_sum s hu
  apply le_trans (mixed_mono (by norm_num : ENNReal.ofReal (15/8 : ℝ) ≠ 0)
    ENNReal.ofReal_ne_top (hsum.norm.mul hh.norm) ?_)
    (mixed_sum_le s (by norm_num : (1 : ℝ≥0∞) ≤ 5)
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (15/8 : ℝ)) ENNReal.ofReal_ne_top
      (fun i => normProduct (u i) h) (fun i hi => (hu i hi).norm.mul hh.norm))
  intro t x
  have hnonneg : 0 ≤ ∑ i ∈ s, normProduct (u i) h t x :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [Real.norm_of_nonneg hnonneg]
  simp only [normProduct, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    ‖∑ i ∈ s, u i t x‖ * ‖h t x‖ ≤ (∑ i ∈ s, ‖u i t x‖) * ‖h t x‖ :=
      mul_le_mul_of_nonneg_right (norm_sum_le s _) (norm_nonneg _)
    _ = ∑ i ∈ s, ‖u i t x‖ * ‖h t x‖ := by rw [Finset.sum_mul]

end HartreeF.FreeValueFullCandidate
