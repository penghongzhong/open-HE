import FCompactCrossOffDiagonal

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HartreeF.CompactCross
open ForcingDomain DerivativeMajorization TimeHolder WeakHartreeChain

/-- The two actual differentiated pure cross-potentials decay with support distance.
The input derivative acts on the density; no singular-kernel derivative is used. -/
theorem pure_cross_offDiagonal {α c D : ℝ} (hHLS : OrdinaryHLS α c) (hD : 0 < D)
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
    (htime : ∀ t, t ∉ I → (∀ x, u t x = 0) ∨ (∀ x, v t x = 0))
    (hsep : ∀ x ∈ T, ∀ y ∈ S, D ≤ ‖x-y‖) :
    forcingNorm (innerCross α c u h v) ≠ ∞ ∧
    forcingNorm (outerCross α c u v k) ≠ ∞ ∧
    forcingNorm (innerCross α c u h v) ≤
      ENNReal.ofReal (c*D^(α-3)*((3+α)*U^(2+α)*H)*(volume S).toReal*(V^(2+α))) *
        volume T ^ (5/6 : ℝ) * volume I ^ (1/2 : ℝ) ∧
    forcingNorm (outerCross α c u v k) ≤
      ENNReal.ofReal (c*D^(α-3)*(U^(3+α))*(volume S).toReal*((2+α)*V^(1+α)*K)) *
        volume T ^ (5/6 : ℝ) * volume I ^ (1/2 : ℝ) := by
  have ha := hHLS.order_pos
  have hden : Continuous (fun z : ℝ × Space => directionalDensity α (u z.1) (h z.1) z.2) :=
    ((densityDerivative_continuous (by linarith : 1 < 3+α)).comp hu).clm_apply hh
  have hloc : Continuous (fun z : ℝ × Space => WeakHartreeChain.localFactor (1+α) (v z.1 z.2)) :=
    (localFactor_contDiff_one (by linarith : 1 < 1+α)).continuous.comp hv
  have hpow : Continuous (fun z : ℝ × Space => powerDensity α (u z.1) z.2) :=
    (density_contDiff_one (by linarith : 1 < 3+α)).continuous.comp hu
  have hder : Continuous (fun z : ℝ × Space => localFactorDerivative (1+α) (v z.1 z.2) (k z.1 z.2)) :=
    ((localFactorDerivative_continuous (by linarith : 1 < 1+α)).comp hv).clm_apply hk
  have hinner := convolution_product_offDiagonal
    (g := fun t => directionalDensity α (u t) (h t))
    (f := fun t x => WeakHartreeChain.localFactor (1+α) (v t x))
    hHLS.order_lt_three hHLS.normalization_pos.le hD
    (by positivity : 0 ≤ (3+α)*U^(2+α)*H) (by positivity : 0 ≤ V^(2+α))
    hS hT hI hSf hTf hIf hden.measurable hloc.measurable
    (fun t x => density_action_amplitude ha hU hH (huB t x) (hhB t x))
    (by
      intro t x
      rw [localFactor_norm (by linarith : 0 < 1+α), show 1+α+1=2+α by ring]
      exact Real.rpow_le_rpow (norm_nonneg _) (hvB t x) (by linarith))
    (by intro t x hx; simp [directionalDensity,huS t x hx,densityDerivative_zero])
    (by intro t x hx; simp [WeakHartreeChain.localFactor,hvT t x hx])
    (by
      intro t ht
      rcases htime t ht with ht | ht
      · left; intro x; simp [directionalDensity,ht x,densityDerivative_zero]
      · right; intro x; simp [WeakHartreeChain.localFactor,ht x]) hsep
  have houter := convolution_product_offDiagonal
    (g := fun t => powerDensity α (u t))
    (f := fun t x => localFactorDerivative (1+α) (v t x) (k t x))
    hHLS.order_lt_three hHLS.normalization_pos.le hD
    (by positivity : 0 ≤ U^(3+α)) (by positivity : 0 ≤ (2+α)*V^(1+α)*K)
    hS hT hI hSf hTf hIf hpow.measurable hder.measurable
    (by
      intro t x
      rw [powerDensity,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact Real.rpow_le_rpow (norm_nonneg _) (huB t x) (by linarith))
    (fun t x => local_action_amplitude ha hV hK (hvB t x) (hkB t x))
    (by intro t x hx; simp [powerDensity,huS t x hx,Real.zero_rpow (by linarith : 3+α ≠ 0)])
    (by intro t x hx; simp [hvT t x hx,localFactorDerivative_zero (by linarith : 0 < 1+α)])
    (by
      intro t ht
      rcases htime t ht with ht | ht
      · left; intro x; simp [powerDensity,ht x,Real.zero_rpow (by linarith : 3+α ≠ 0)]
      · right; intro x; simp [ht x,localFactorDerivative_zero (by linarith : 0 < 1+α)]) hsep
  exact ⟨hinner.2.1,houter.2.1,hinner.2.2,houter.2.2⟩

#print axioms pure_cross_offDiagonal
end HartreeF.CompactCross
