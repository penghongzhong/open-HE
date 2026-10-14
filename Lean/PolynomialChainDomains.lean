import DensityGradientDomains

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.WeakHartreeChain

def complexChainGradient (F : ℂ → ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → Space :=
  fun x => (fderiv ℝ F (u x) 1) • U x+(fderiv ℝ F (u x) Complex.I) • V x

def powerGradientMajorant (q : ℝ) (u : Space → ℂ) (U V : Space → Space) : Space → ℝ :=
  fun x => ‖u x‖^q*(‖U x‖+‖V x‖)

theorem powerGradientMajorant_memLp {q : ℝ} (hq : 0 < q)
    {u : Space → ℂ} {U V : Space → Space} (hu : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (powerGradientMajorant q u U V) (ENNReal.ofReal (30/(3*q+13))) volume := by
  have hpow : MemLp (fun x => ‖u x‖^q) (ENNReal.ofReal (10/q)) volume :=
    ForcingDomain.norm_power_memLp hq (by simpa using hu)
  have hh : Real.HolderTriple (10/q) (30/13) (30/(3*q+13)) := by
    constructor
    · field_simp
      ring
    · positivity
    · norm_num
  let := hh.ennrealOfReal
  exact hpow.mul (hU.norm.add hV.norm)

theorem complexChainGradient_bound {F : ℂ → ℝ} {q C : ℝ}
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C*‖z‖^q)
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    ‖complexChainGradient F u U V x‖ ≤ C*powerGradientMajorant q u U V x := by
  have he (e : ℂ) (hne : ‖e‖ = 1) : ‖fderiv ℝ F (u x) e‖ ≤ C*‖u x‖^q := by
    exact ((fderiv ℝ F (u x)).le_opNorm e).trans (by simpa only [hne,mul_one] using hbound (u x))
  calc
    _ ≤ ‖(fderiv ℝ F (u x) 1) • U x‖+‖(fderiv ℝ F (u x) Complex.I) • V x‖ := norm_add_le _ _
    _ ≤ (C*‖u x‖^q)*‖U x‖+(C*‖u x‖^q)*‖V x‖ := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_right (he 1 (by simp)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (he Complex.I (by simp)) (norm_nonneg _))
    _ = _ := by unfold powerGradientMajorant; ring

theorem complexChainGradient_aestronglyMeasurable {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F)
    {u : Space → ℂ} {U V : Space → Space}
    (hu : AEStronglyMeasurable u volume) (hU : AEStronglyMeasurable U volume)
    (hV : AEStronglyMeasurable V volume) :
    AEStronglyMeasurable (complexChainGradient F u U V) volume := by
  have hc := hF.continuous_fderiv (by simp)
  exact (((hc.clm_apply continuous_const).comp_aestronglyMeasurable hu).smul hU).add
    (((hc.clm_apply continuous_const).comp_aestronglyMeasurable hu).smul hV)

theorem complexChainGradient_memLp {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F)
    {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C*‖z‖^q)
    {u : Space → ℂ} {U V : Space → Space} (hu : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    MemLp (complexChainGradient F u U V) (ENNReal.ofReal (30/(3*q+13))) volume := by
  apply ((powerGradientMajorant_memLp hq hu hU hV).const_mul C).of_le
    (complexChainGradient_aestronglyMeasurable hF hu.aestronglyMeasurable hU.aestronglyMeasurable hV.aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [powerGradientMajorant,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hC
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (add_nonneg (norm_nonneg _) (norm_nonneg _))))] using
    complexChainGradient_bound hbound u U V x

theorem polynomial_composition_memLp {F : ℂ → ℝ} (hF : Continuous F)
    {m D t : ℝ} (hm : 0 < m) (hD : 0 ≤ D)
    (hbound : ∀ z, ‖F z‖ ≤ D*‖z‖^m)
    {u : Space → ℂ} (hu : MemLp u (ENNReal.ofReal t) volume) :
    MemLp (fun x => F (u x)) (ENNReal.ofReal (t/m)) volume := by
  apply ((ForcingDomain.norm_power_memLp hm hu).const_mul D).of_le
    (hF.comp_aestronglyMeasurable hu.aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hD (Real.rpow_nonneg (norm_nonneg _) _))] using hbound (u x)

theorem complexChainGradient_tendsto {F : ℂ → ℝ} {Fn : ℕ → ℂ → ℝ}
    (ht : ∀ z, Tendsto (fun n => fderiv ℝ (Fn n) z) atTop (𝓝 (fderiv ℝ F z)))
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    Tendsto (fun n => complexChainGradient (Fn n) u U V x) atTop
      (𝓝 (complexChainGradient F u U V x)) := by
  have he (e : ℂ) := ((ContinuousLinearMap.apply ℝ ℝ e).continuous.tendsto (fderiv ℝ F (u x))).comp (ht (u x))
  exact ((he 1).smul (tendsto_const_nhds (x := U x))).add
    ((he Complex.I).smul (tendsto_const_nhds (x := V x)))

#print axioms powerGradientMajorant_memLp
#print axioms complexChainGradient_bound
#print axioms complexChainGradient_aestronglyMeasurable
#print axioms complexChainGradient_memLp
#print axioms polynomial_composition_memLp
#print axioms complexChainGradient_tendsto
end HartreeF.WeakHartreeChain
