import FStateAffineForcing
import FWeakSourceAffinePullback
import HartreeForcingWeakGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.AffineForcing
open CriticalAffine ForcingDomain SobolevStretch StationarySelfTest WeakHartreeProduct

/-- The actual original Hartree weak-gradient producer and its L6/5 domains
feed the separate source pullback. No forcing EnergyState is assumed. -/
theorem forcing_affine_weak_gradients (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) {alpha c : ℝ} (hH : OrdinaryHLS alpha c)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13:ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13:ℝ)) volume)
    {a : ℝ} (ha : 0<a) (b : Space) :
    HasWeakGradient (fun x => (forcing alpha c (valuePullback a b u) x).re)
      (fun x => a^(7/2:ℝ) • forcingGradientRe alpha c u U V (affine a b x)) ∧
    HasWeakGradient (fun x => (forcing alpha c (valuePullback a b u) x).im)
      (fun x => a^(7/2:ℝ) • forcingGradientIm alpha c u U V (affine a b x)) ∧
    MemLp (forcing alpha c (valuePullback a b u)) (ENNReal.ofReal (6/5:ℝ)) volume ∧
    MemLp (fun x => a^(7/2:ℝ) • forcingGradientRe alpha c u U V (affine a b x))
      (ENNReal.ofReal (6/5:ℝ)) volume ∧
    MemLp (fun x => a^(7/2:ℝ) • forcingGradientIm alpha c u U V (affine a b x))
      (ENNReal.ofReal (6/5:ℝ)) volume := by
  have hw := hartree_forcing_weak_gradients hDensity hSob hH hu hu10 hU hV
  have hg := hartree_forcing_gradient_domains hH hu.function_L6 hu10 hU hV
  obtain ⟨C,hC⟩ := forcing_energy_domain_bound hH
  have hn := (hC u hu.function_L6).1
  have hr := hasWeakGradient_affine_memLp hw.1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hn.continuousLinearMap_comp Complex.reCLM) hg.1 ha b (a^(5/2:ℝ))
  have hi := hasWeakGradient_affine_memLp hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (hn.continuousLinearMap_comp Complex.imCLM) hg.2 ha b (a^(5/2:ℝ))
  have hk : a^(5/2:ℝ)*a=a^(7/2:ℝ) := by
    calc
      _ = a^(5/2:ℝ)*a^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add ha]; norm_num
  have hfr : (fun x => (forcing alpha c (valuePullback a b u) x).re)=
      (fun x => a^(5/2:ℝ)*(forcing alpha c u (affine a b x)).re) := by
    funext x
    rw [forcing_valuePullback alpha c ha b]
    simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hfi : (fun x => (forcing alpha c (valuePullback a b u) x).im)=
      (fun x => a^(5/2:ℝ)*(forcing alpha c u (affine a b x)).im) := by
    funext x
    rw [forcing_valuePullback alpha c ha b]
    simp only [Complex.real_smul,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  refine ⟨?_,?_,(hC _ (valuePullback_memLp ha b (by norm_num) (by norm_num) hu.function_L6)).1,
    (affine_memLp ha.ne' b (by norm_num) (by norm_num) hg.1).const_smul (a^(7/2:ℝ)),
    (affine_memLp ha.ne' b (by norm_num) (by norm_num) hg.2).const_smul (a^(7/2:ℝ))⟩
  · rw [hfr]
    simpa only [hk] using hr
  · rw [hfi]
    simpa only [hk] using hi

#print axioms forcing_affine_weak_gradients
end HartreeF.AffineForcing
