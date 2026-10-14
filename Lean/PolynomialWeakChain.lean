import RetractedComplexCalculus
import PolynomialChainDomains
import DensityWeakGradient

/-! A proved polynomial-growth C1 Nemytskii theorem from the native bounded
chain and an explicit radial retraction. This is not an external chain interface. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.WeakHartreeChain
open SobolevStretch StationarySelfTest WeakLpClosure

theorem polynomial_C1_hasWeakGradient (hDensity : OrdinaryH1Density)
    {F : ℂ → ℝ} (hF : ContDiff ℝ 1 F) (hz : F 0 = 0)
    {q C D : ℝ} (hq : 1 < q) (hq4 : q < 4) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hfb : ∀ z, ‖F z‖ ≤ D*‖z‖^(q+1))
    (hdb : ∀ z, ‖fderiv ℝ F z‖ ≤ C*‖z‖^q)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => F (u x)) (complexChainGradient F u U V) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q+1 := by linarith
  let Fn : ℕ → ℂ → ℝ := fun n => retractedMap F (saturationParameter n)
  have hFn (n : ℕ) : ContDiff ℝ 1 (Fn n) := retractedMap_contDiff_one hF (saturationParameter_pos n).le
  have hFnb (n : ℕ) (z : ℂ) : ‖Fn n z‖ ≤ D*‖z‖^(q+1) :=
    retractedMap_norm_bound hq1.le hD (saturationParameter_pos n).le hfb z
  have hFnd (n : ℕ) (z : ℂ) : ‖fderiv ℝ (Fn n) z‖ ≤ (3*C)*‖z‖^q :=
    retractedMap_fderiv_bound hF hq0.le hC (saturationParameter_pos n).le hdb z
  have hw (n : ℕ) : HasWeakGradient (fun x => Fn n (u x)) (complexChainGradient (Fn n) u U V) := by
    have he := saturationParameter_pos n
    let B : ℝ≥0 := ⟨(3*C)*(1+(saturationParameter n)⁻¹)^q, by positivity⟩
    exact hasWeakGradient_bounded_complex_comp_dotH1 hDensity (B := B) (hFn n)
      (retractedMap_zero hz _) (retractedMap_fderiv_bounded hF hq0.le hC (saturationParameter_pos n) hdb) hu
  have hf := polynomial_composition_memLp hF.continuous hq1 hD hfb
    (show MemLp u (ENNReal.ofReal 6) volume by simpa using hu.function_L6)
  have hfn (n : ℕ) := polynomial_composition_memLp (hFn n).continuous hq1 hD (hFnb n)
    (show MemLp u (ENNReal.ofReal 6) volume by simpa using hu.function_L6)
  have hg := complexChainGradient_memLp hF hq0 hC hdb hu10 hU hV
  have hgn (n : ℕ) := complexChainGradient_memLp (hFn n) hq0 (by positivity : 0 ≤ 3*C) (hFnd n) hu10 hU hV
  have hd : Real.HolderTriple (6/(5-q)) (6/(q+1)) 1 := by
    constructor
    · field_simp
      ring
    · exact div_pos (by norm_num) (by linarith)
    · positivity
  have ht : Real.HolderTriple (30/(17-3*q)) (30/(3*q+13)) 1 := by
    constructor
    · field_simp
      ring
    · exact div_pos (by norm_num) (by linarith)
    · positivity
  let : ENNReal.HolderTriple (ENNReal.ofReal (6/(5-q))) (ENNReal.ofReal (6/(q+1))) 1 := by
    simpa only [ENNReal.ofReal_one] using hd.ennrealOfReal
  let : ENNReal.HolderTriple (ENNReal.ofReal (30/(17-3*q))) (ENNReal.ofReal (30/(3*q+13))) 1 := by
    simpa only [ENNReal.ofReal_one] using ht.ennrealOfReal
  apply hasWeakGradient_of_mixed_Lp_limit
    (p' := ENNReal.ofReal (6/(5-q))) (q' := ENNReal.ofReal (30/(17-3*q)))
    (p := ENNReal.ofReal (6/(q+1))) (q := ENNReal.ofReal (30/(3*q+13)))
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hq1).mpr (by linarith)))
    (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ (by linarith : 0 < 3*q+13)).mpr (by linarith)))
    hf hg hfn hgn hw
  · have hdom := (ForcingDomain.norm_power_memLp hq1
      (show MemLp u (ENNReal.ofReal 6) volume by simpa using hu.function_L6)).const_mul (2*D)
    apply strong_lp_zero_of_ae_dominated (by positivity) ENNReal.ofReal_ne_top
      (fun n => (hfn n).aestronglyMeasurable.sub hf.aestronglyMeasurable) hdom
    · intro n
      filter_upwards [] with x
      change ‖Fn n (u x)-F (u x)‖ ≤ ‖(2*D)*‖u x‖^(q+1)‖
      rw [show ‖(2*D)*‖u x‖^(q+1)‖ = (2*D)*‖u x‖^(q+1) from
        Real.norm_of_nonneg (by positivity)]
      have hb := norm_sub_le (Fn n (u x)) (F (u x))
      linarith [hFnb n (u x),hfb (u x)]
    · filter_upwards [] with x
      simpa only [Pi.sub_apply,sub_self] using (retractedMap_tendsto hF.continuous (u x)).sub
        (tendsto_const_nhds (x := F (u x)))
  · have hdom := (powerGradientMajorant_memLp hq0 hu10 hU hV).const_mul (4*C)
    apply strong_lp_zero_of_ae_dominated (by positivity) ENNReal.ofReal_ne_top
      (fun n => (hgn n).aestronglyMeasurable.sub hg.aestronglyMeasurable) hdom
    · intro n
      filter_upwards [] with x
      change ‖complexChainGradient (Fn n) u U V x-complexChainGradient F u U V x‖ ≤
        ‖(4*C)*powerGradientMajorant q u U V x‖
      have hM : 0 ≤ powerGradientMajorant q u U V x := by unfold powerGradientMajorant; positivity
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity) hM)]
      have hb := norm_sub_le (complexChainGradient (Fn n) u U V x) (complexChainGradient F u U V x)
      linarith [complexChainGradient_bound (hFnd n) u U V x,complexChainGradient_bound hdb u U V x]
    · filter_upwards [] with x
      simpa only [Pi.sub_apply,sub_self] using
        (complexChainGradient_tendsto (retractedMap_fderiv_tendsto hF) u U V x).sub
          (tendsto_const_nhds (x := complexChainGradient F u U V x))

#print axioms polynomial_C1_hasWeakGradient
end HartreeF.WeakHartreeChain
