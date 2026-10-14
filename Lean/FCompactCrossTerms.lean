import FCompactCrossTime

/-! The actual two pure cross-potential derivative terms, with independent complex
value and directional fields. No derivative identity or scalar estimate is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain DerivativeMajorization TimeHolder WeakHartreeChain

def innerCross (α c : ℝ) (u h v : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x => rieszConvolution α c (directionalDensity α (u t) (h t)) x •
    WeakHartreeChain.localFactor (1+α) (v t x)

def outerCross (α c : ℝ) (u v k : ℝ → Space → ℂ) : ℝ → Space → ℂ :=
  fun t x => potential α c (u t) x • localFactorDerivative (1+α) (v t x) (k t x)

def forcingNorm (f : ℝ → Space → ℂ) : ℝ≥0∞ :=
  mixedNorm volume volume 2 (ENNReal.ofReal (6/5 : ℝ)) f

theorem density_action_amplitude {α U H : ℝ} (ha : 0 < α) (hU : 0 ≤ U) (_hH : 0 ≤ H)
    {z w : ℂ} (hz : ‖z‖ ≤ U) (hw : ‖w‖ ≤ H) :
    ‖densityDerivative (3+α) z w‖ ≤ (3+α) * U^(2+α) * H := by
  calc
    _ ≤ ‖densityDerivative (3+α) z‖ * ‖w‖ := (densityDerivative (3+α) z).le_opNorm w
    _ = (3+α) * ‖z‖^(2+α) * ‖w‖ := by
      rw [densityDerivative_norm (by linarith), show 3+α-1=2+α by ring]
    _ ≤ _ := by gcongr

theorem local_action_amplitude {α V K : ℝ} (ha : 0 < α) (hV : 0 ≤ V) (_hK : 0 ≤ K)
    {z w : ℂ} (hz : ‖z‖ ≤ V) (hw : ‖w‖ ≤ K) :
    ‖localFactorDerivative (1+α) z w‖ ≤ (2+α) * V^(1+α) * K := by
  calc
    _ ≤ ‖localFactorDerivative (1+α) z‖ * ‖w‖ := (localFactorDerivative (1+α) z).le_opNorm w
    _ ≤ ((1+α)+1) * ‖z‖^(1+α) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (localFactorDerivative_bound (by linarith) z) (norm_nonneg w)
    _ = (2+α) * ‖z‖^(1+α) * ‖w‖ := by ring
    _ ≤ _ := by gcongr

/-- Both differentiated pure cross-potentials have finite literal mixed norm.
All assumptions concern the actual input fields, their amplitudes and supports. -/
theorem pure_cross_time_support_bound {α c q r s : ℝ} (hHLS : OrdinaryHLS α c)
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
      (∀ t, t ∉ I → (∀ x, u t x = 0) ∨ (∀ x, v t x = 0)) →
      forcingNorm (innerCross α c u h v) ≠ ∞ ∧
      forcingNorm (outerCross α c u v k) ≠ ∞ ∧
      forcingNorm (innerCross α c u h v) ≤
        (C : ℝ≥0∞) * (ENNReal.ofReal ((3+α)*U^(2+α)*H) * volume S ^ (1/q)) *
          (ENNReal.ofReal (V^(2+α)) * volume T ^ (1/s)) * volume I ^ (1/2 : ℝ) ∧
      forcingNorm (outerCross α c u v k) ≤
        (C : ℝ≥0∞) * (ENNReal.ofReal (U^(3+α)) * volume S ^ (1/q)) *
          (ENNReal.ofReal ((2+α)*V^(1+α)*K) * volume T ^ (1/s)) * volume I ^ (1/2 : ℝ) := by
  have ha := hHLS.order_pos
  obtain ⟨C,hC⟩ := convolution_product_time_support_bound hHLS hq1 hqα hr hrel hholder
  refine ⟨C, fun S T I hS hT hI hSf hTf hIf U H V K hU hH hV hK u h v k hu hh hv hk
    huB hhB hvB hkB huS hvT htime => ?_⟩
  have hden : Continuous (fun z : ℝ × Space => directionalDensity α (u z.1) (h z.1) z.2) :=
    ((densityDerivative_continuous (by linarith : 1 < 3+α)).comp hu).clm_apply hh
  have hloc : Continuous (fun z : ℝ × Space => WeakHartreeChain.localFactor (1+α) (v z.1 z.2)) :=
    (localFactor_contDiff_one (by linarith : 1 < 1+α)).continuous.comp hv
  have hpow : Continuous (fun z : ℝ × Space => powerDensity α (u z.1) z.2) :=
    (density_contDiff_one (by linarith : 1 < 3+α)).continuous.comp hu
  have hder : Continuous (fun z : ℝ × Space => localFactorDerivative (1+α) (v z.1 z.2) (k z.1 z.2)) :=
    ((localFactorDerivative_continuous (by linarith : 1 < 1+α)).comp hv).clm_apply hk
  have hinner := hC S T I hS hT hI hSf hTf hIf ((3+α)*U^(2+α)*H) (V^(2+α))
    (by positivity) (by positivity)
    (fun t => directionalDensity α (u t) (h t))
    (fun t x => WeakHartreeChain.localFactor (1+α) (v t x)) hden.measurable hloc.measurable
    (fun t x => density_action_amplitude ha hU hH (huB t x) (hhB t x))
    (by intro t x hx; simp [directionalDensity,huS t x hx,densityDerivative_zero])
    (by
      intro t x
      rw [localFactor_norm (by linarith : 0 < 1+α), show 1+α+1=2+α by ring]
      exact Real.rpow_le_rpow (norm_nonneg _) (hvB t x) (by linarith))
    (by intro t x hx; simp [WeakHartreeChain.localFactor,hvT t x hx])
    (by
      intro t ht
      rcases htime t ht with ht | ht
      · left; intro x; simp [directionalDensity,ht x,densityDerivative_zero]
      · right; intro x; simp [WeakHartreeChain.localFactor,ht x])
  have houter := hC S T I hS hT hI hSf hTf hIf (U^(3+α)) ((2+α)*V^(1+α)*K)
    (by positivity) (by positivity)
    (fun t => powerDensity α (u t))
    (fun t x => localFactorDerivative (1+α) (v t x) (k t x)) hpow.measurable hder.measurable
    (by
      intro t x
      rw [powerDensity,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow (norm_nonneg _) (huB t x) (by linarith))
    (by intro t x hx; simp [powerDensity,huS t x hx,Real.zero_rpow (by linarith : 3+α ≠ 0)])
    (fun t x => local_action_amplitude ha hV hK (hvB t x) (hkB t x))
    (by intro t x hx; simp [hvT t x hx,localFactorDerivative_zero (by linarith : 0 < 1+α)])
    (by
      intro t ht
      rcases htime t ht with ht | ht
      · left; intro x; simp [powerDensity,ht x,Real.zero_rpow (by linarith : 3+α ≠ 0)]
      · right; intro x; simp [ht x,localFactorDerivative_zero (by linarith : 0 < 1+α)])
  exact ⟨hinner.2.1,houter.2.1,hinner.2.2,houter.2.2⟩

#print axioms density_action_amplitude
#print axioms local_action_amplitude
#print axioms pure_cross_time_support_bound
end HartreeF.CompactCross
