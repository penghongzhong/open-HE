import FCriticalAffineWeakGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.AffineForcing
open CriticalAffine SobolevStretch

/-- The same compact-test change of variables works in genuine finite Lp
source domains. It does not require a value-L6/gradient-L2 EnergyState. -/
theorem hasWeakGradient_affine_memLp {f : Space → ℝ} {G : Space → Space}
    (h : HasWeakGradient f G) {p q : ℝ≥0∞} (hp : 1≤p) (hptop : p≠∞)
    (hq : 1≤q) (hqtop : q≠∞) (hf : MemLp f p volume) (hG : MemLp G q volume)
    {a : ℝ} (ha : 0<a) (b : Space) (k : ℝ) :
    HasWeakGradient (fun x => k*f (affine a b x)) (fun x => (k*a) • G (affine a b x)) := by
  have hp0 : p≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<1) hp)
  have hq0 : q≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞)<1) hq)
  refine ⟨((affine_memLp ha.ne' b hp0 hptop hf).const_mul k).locallyIntegrable hp,
    ((affine_memLp ha.ne' b hq0 hqtop hG).const_smul (k*a)).locallyIntegrable hq, ?_⟩
  intro v φ hφ hc
  let ψ : Space → ℝ := fun y => φ (a⁻¹ • (y-b))
  have ht := inverse_affine_test_class ha b hφ hc
  have hw := h.integration_by_parts (a • v) ψ ht.1 ht.2
  have hj1 := affine_integral ha b (fun y => f y*fderiv ℝ ψ y (a • v))
  have hj2 := affine_integral ha b (fun y => inner ℝ (G y) (a • v)*ψ y)
  have hd (x : Space) : fderiv ℝ ψ (affine a b x) (a • v)=fderiv ℝ φ x v := by
    rw [inverse_affine_test_derivative ha b hφ]
    simp [affine,smul_smul,ha.ne']
  have hv (x : Space) : ψ (affine a b x)=φ x := by
    simp [ψ,affine,smul_smul,ha.ne']
  simp only [hd,smul_eq_mul] at hj1
  simp only [hv,smul_eq_mul] at hj2
  have he : (∫ x, f (affine a b x)*fderiv ℝ φ x v)=
      -(∫ x, inner ℝ (G (affine a b x)) (a • v)*φ x) := by
    rw [hj1,hw,mul_neg,← hj2]
  have hg (x : Space) : inner ℝ ((k*a) • G (affine a b x)) v=
      k*inner ℝ (G (affine a b x)) (a • v) := by
    simp only [real_inner_smul_left,real_inner_smul_right]
    ring
  simp only [hg,mul_assoc,integral_const_mul,he,mul_neg]

#print axioms hasWeakGradient_affine_memLp
end HartreeF.AffineForcing
