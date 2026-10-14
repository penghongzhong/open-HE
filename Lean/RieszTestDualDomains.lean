import RieszKernelTestCalculus

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.RieszWeakDerivative
open ForcingDomain GradientMajorants

theorem riesz_compact_dual_memLp {α c s : ℝ} (hH : OrdinaryHLS α c)
    (hs : α/3 < s) (hs1 : s < 1)
    {φ : Space → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    MemLp (rieszConvolution α c φ) (ENNReal.ofReal (1/(1-s))) volume := by
  have hdlo : α/3 < 1-s+α/3 := by linarith
  have hdhi : 1-s+α/3 < 1 := by linarith
  obtain ⟨hp1,hpα,_,_⟩ := reciprocal_hls_range hH.order_pos hdlo hdhi
  obtain ⟨C,hC⟩ := hH.strong_bound (1/(1-s+α/3)) (1/(1-s)) hp1 hpα
    (by positivity) (by simp)
  exact (hC φ (hφ.memLp_of_hasCompactSupport hc)).2.1

theorem riesz_test_dual_derivative_memLp {α c s : ℝ} (hH : OrdinaryHLS α c)
    (hs : α/3 < s) (hs1 : s < 1)
    {φ : Space → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (v : Space) :
    MemLp (fun x => fderiv ℝ (rieszConvolution α c φ) x v) (ENNReal.ofReal (1/(1-s))) volume := by
  simp_rw [riesz_test_fderiv hH.order_pos hφ hc]
  exact riesz_compact_dual_memLp hH hs hs1
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ v)

theorem reciprocal_holder {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ENNReal.HolderTriple (ENNReal.ofReal (1/s)) (ENNReal.ofReal (1/(1-s))) 1 := by
  have hh : Real.HolderTriple (1/s) (1/(1-s)) 1 := by
    constructor
    · simp
    · positivity
    · positivity
  simpa only [ENNReal.ofReal_one] using hh.ennrealOfReal

theorem riesz_output_test_holder {α s : ℝ} (hα : 0 < α) (hs : α/3 < s) (hs1 : s < 1) :
    ENNReal.HolderTriple (ENNReal.ofReal (1/(s-α/3)))
      (ENNReal.ofReal (1/(1-s+α/3))) 1 := by
  have hh : Real.HolderTriple (1/(s-α/3)) (1/(1-s+α/3)) 1 := by
    constructor
    · simp
    · exact div_pos (by norm_num) (by linarith)
    · exact div_pos (by norm_num) (by linarith)
  simpa only [ENNReal.ofReal_one] using hh.ennrealOfReal

#print axioms riesz_compact_dual_memLp
#print axioms riesz_test_dual_derivative_memLp
#print axioms reciprocal_holder
#print axioms riesz_output_test_holder
end HartreeF.RieszWeakDerivative
