import SaturatedDensityWeakGradient

/-! Actual weak Nemytskii differentiation for |u|^p by bounded-C1 saturation.
The final theorem supplies all domains from L6, L10 and the actual weak gradients.
The auxiliary exponent 30/(3p+10) only identifies the derivative; it is not an HLS input. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.WeakHartreeChain
open SobolevStretch StationarySelfTest WeakLpClosure

theorem density_hasWeakGradient_of_domains (hDensity : OrdinaryH1Density)
    {p : ℝ} (hp : 1 < p) {r s r' s' : ℝ≥0∞}
    [ENNReal.HolderTriple r' r 1] [ENNReal.HolderTriple s' s 1]
    (hr : 1 ≤ r) (hs : 1 ≤ s) (hrt : r ≠ ∞) (hst : s ≠ ∞)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hb : MemLp (fun x => density p (u x)) r volume)
    (hG : MemLp (densityGradient p u U V) s volume) :
    HasWeakGradient (fun x => density p (u x)) (densityGradient p u U V) := by
  let fn : ℕ → Space → ℝ := fun n x => saturatedDensity p (saturationParameter n) (u x)
  let cn : ℕ → Space → ℝ := fun n x => saturationCoeff p (saturationParameter n) (u x)
  let Gn : ℕ → Space → Space := fun n x => cn n x • densityGradient p u U V x
  have hfm (n : ℕ) : AEStronglyMeasurable (fn n) volume :=
    (saturatedDensity_contDiff_one hp (saturationParameter_pos n).le).continuous.comp_aestronglyMeasurable
      hu.function_L6.aestronglyMeasurable
  have hcm (n : ℕ) : AEStronglyMeasurable (cn n) volume :=
    (saturationCoeff_continuous hp (saturationParameter_pos n).le).comp_aestronglyMeasurable
      hu.function_L6.aestronglyMeasurable
  have hc0 (n : ℕ) (x : Space) : 0 ≤ cn n x := saturationCoeff_nonneg p (u x)
  have hc1 (n : ℕ) (x : Space) : cn n x ≤ 1 :=
    saturationCoeff_le_one (saturationParameter_pos n).le p (u x)
  have hfb (n : ℕ) (x : Space) : ‖fn n x‖ ≤ ‖density p (u x)‖ := by
    simpa only [fn,Real.norm_eq_abs,abs_of_nonneg (saturatedDensity_nonneg
      (saturationParameter_pos n).le p (u x)),abs_of_nonneg (density_nonneg p (u x))] using
      saturatedDensity_le_density (saturationParameter_pos n).le p (u x)
  have hgb (n : ℕ) (x : Space) : ‖Gn n x‖ ≤ ‖densityGradient p u U V x‖ := by
    change ‖cn n x • densityGradient p u U V x‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hc0 n x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc1 n x)
  have hfn (n : ℕ) : MemLp (fn n) r volume := hb.of_le (hfm n) (ae_of_all _ (hfb n))
  have hgn (n : ℕ) : MemLp (Gn n) s volume :=
    hG.of_le ((hcm n).smul hG.aestronglyMeasurable) (ae_of_all _ (hgb n))
  apply hasWeakGradient_of_mixed_Lp_limit (p' := r') (q' := s') hr hs hb hG hfn hgn
    (fun n => saturatedDensity_hasWeakGradient hDensity hp (saturationParameter_pos n) hu)
  · apply strong_lp_zero_of_ae_dominated (ne_of_gt (lt_of_lt_of_le zero_lt_one hr)) hrt
      (fun n => (hfm n).sub hb.aestronglyMeasurable) hb
    · intro n
      filter_upwards [] with x
      change ‖fn n x-density p (u x)‖ ≤ ‖density p (u x)‖
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (density_nonneg p (u x))]
      have hlo := saturatedDensity_nonneg (saturationParameter_pos n).le p (u x)
      have hhi := saturatedDensity_le_density (saturationParameter_pos n).le p (u x)
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    · filter_upwards [] with x
      simpa only [fn,Pi.sub_apply,sub_self] using (saturatedDensity_tendsto p (u x)).sub
        (tendsto_const_nhds (x := density p (u x)))
  · apply strong_lp_zero_of_ae_dominated (ne_of_gt (lt_of_lt_of_le zero_lt_one hs)) hst
      (fun n => (hgn n).aestronglyMeasurable.sub hG.aestronglyMeasurable) hG
    · intro n
      filter_upwards [] with x
      change ‖cn n x • densityGradient p u U V x-densityGradient p u U V x‖ ≤ _
      have he : cn n x • densityGradient p u U V x-densityGradient p u U V x =
          (cn n x-1) • densityGradient p u U V x := by rw [sub_smul,one_smul]
      rw [he,norm_smul,Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr ⟨by linarith [hc0 n x],by linarith [hc1 n x]⟩)
    · filter_upwards [] with x
      simpa only [Gn,cn,Pi.sub_apply,one_smul,sub_self] using
        ((saturationCoeff_tendsto p (u x)).smul
          (tendsto_const_nhds (x := densityGradient p u U V x))).sub
          (tendsto_const_nhds (x := densityGradient p u U V x))

theorem density_hasWeakGradient (hDensity : OrdinaryH1Density)
    {p : ℝ} (hp : 3 < p) (hp6 : p < 6)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hu10 : MemLp u 10 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    HasWeakGradient (fun x => density p (u x)) (densityGradient p u U V) := by
  have hp0 : 0 < p := by linarith
  have hd : Real.HolderTriple (6/(6-p)) (6/p) 1 := by
    constructor
    · field_simp
      ring
    · positivity
    · positivity
  have hg : Real.HolderTriple (30/(20-3*p)) (30/(3*p+10)) 1 := by
    constructor
    · field_simp
      ring
    · exact div_pos (by norm_num) (by linarith)
    · exact div_pos (by norm_num) (by linarith)
  let : ENNReal.HolderTriple (ENNReal.ofReal (6/(6-p))) (ENNReal.ofReal (6/p)) 1 := by
    simpa only [ENNReal.ofReal_one] using hd.ennrealOfReal
  let : ENNReal.HolderTriple (ENNReal.ofReal (30/(20-3*p))) (ENNReal.ofReal (30/(3*p+10))) 1 := by
    simpa only [ENNReal.ofReal_one] using hg.ennrealOfReal
  apply density_hasWeakGradient_of_domains hDensity (by linarith : 1 < p)
    (r' := ENNReal.ofReal (6/(6-p))) (s' := ENNReal.ofReal (30/(20-3*p)))
    (r := ENNReal.ofReal (6/p)) (s := ENNReal.ofReal (30/(3*p+10)))
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hp0).mpr (by linarith))
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ (by linarith : 0 < 3*p+10)).mpr (by linarith))
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top
  · exact hu
  · exact density_Lp hp0 (by simpa using hu.function_L6)
  · exact densityGradient_memLp (by linarith) hu10 hU hV

#print axioms density_hasWeakGradient_of_domains
#print axioms density_hasWeakGradient
end HartreeF.WeakHartreeChain
