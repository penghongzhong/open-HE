import FCompactCrossSeeds

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal
namespace HartreeF.CompactCross
open ForcingDomain DerivativeMajorization WeakHartreeChain TimeHolder AffineMixed

/-- Spatial nonlocality does not mix distinct times: both actual terms vanish. -/
theorem pure_cross_zero_of_time_separation {α : ℝ} (ha : 0 < α) (c : ℝ)
    (u h v k : ℝ → Space → ℂ)
    (htime : ∀ t, (∀ x, u t x = 0) ∨ (∀ x, v t x = 0)) :
    innerCross α c u h v = 0 ∧ outerCross α c u v k = 0 := by
  constructor
  · funext t x
    rcases htime t with ht | ht
    · simp [innerCross,directionalDensity,ht,densityDerivative_zero,rieszConvolution]
    · simp [innerCross,WeakHartreeChain.localFactor,ht]
  · funext t x
    rcases htime t with ht | ht
    · simp [outerCross,potential,powerDensity,ht,Real.zero_rpow (by linarith : 3+α ≠ 0)]
    · simp [outerCross,ht,localFactorDerivative_zero (by linarith : 0 < 1+α)]

theorem pure_cross_norm_zero_of_disjoint_time_support {α : ℝ} (ha : 0 < α) (c : ℝ)
    (u h v k : ℝ → Space → ℂ) {I J : Set ℝ} (hIJ : Disjoint I J)
    (hu : ∀ t, t ∉ I → ∀ x, u t x = 0) (hv : ∀ t, t ∉ J → ∀ x, v t x = 0) :
    forcingNorm (innerCross α c u h v) = 0 ∧ forcingNorm (outerCross α c u v k) = 0 := by
  have h := pure_cross_zero_of_time_separation ha c u h v k (by
    intro t
    by_cases ht : t ∈ I
    · right
      apply hv t
      intro hj
      exact Set.disjoint_left.mp hIJ ht hj
    · exact Or.inl (hu t ht))
  simp [h.1,h.2,forcingNorm,mixedNorm]

/-- Exact disjointness after the existing independent parabolic time pullbacks. -/
theorem pure_cross_parabolic_time_disjoint {α : ℝ} (ha : 0 < α) (c a b : ℝ)
    (y z : Space) (d e : ℝ) (u h v k : ℝ → Space → ℂ) {I J : Set ℝ}
    (hIJ : Disjoint ((timeAffine a d) ⁻¹' I) ((timeAffine b e) ⁻¹' J))
    (hu : ∀ t, t ∉ I → ∀ x, u t x = 0) (hv : ∀ t, t ∉ J → ∀ x, v t x = 0) :
    forcingNorm (innerCross α c (parabolicField a y d (1/2) u)
      (parabolicField a y d (3/2) h) (parabolicField b z e (1/2) v)) = 0 ∧
    forcingNorm (outerCross α c (parabolicField a y d (1/2) u)
      (parabolicField b z e (1/2) v) (parabolicField b z e (3/2) k)) = 0 := by
  exact pure_cross_norm_zero_of_disjoint_time_support ha c _ _ _ _ hIJ
    (parabolicField_time_support a y d (1/2) hu)
    (parabolicField_time_support b z e (1/2) hv)

#print axioms pure_cross_zero_of_time_separation
#print axioms pure_cross_norm_zero_of_disjoint_time_support
#print axioms pure_cross_parabolic_time_disjoint
end HartreeF.CompactCross
