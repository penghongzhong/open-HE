import FMixedPowerVanishing

/-! Actual power-density defect convergence for every 0<alpha<3.
The sequence is bounded in L6 and converges a.e.; strong L6 is not assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.NonlocalBL
open ForcingDomain WeakHartreeChain

def densityDefect (alpha : ℝ) (g f : Space → ℂ) (x : Space) : ℝ :=
  powerDensity alpha (g+f) x-powerDensity alpha g x-powerDensity alpha f x

def densityDefectConstant (alpha : ℝ) : ℝ := (3+alpha)*(2^(2+alpha)+1)+1

theorem densityDefectConstant_pos {alpha : ℝ} (ha : 0 < alpha) :
    0 < densityDefectConstant alpha := by unfold densityDefectConstant; positivity

theorem norm_add_rpow_bound {s : ℝ} (hs : 0 ≤ s) (z w : ℂ) :
    ‖z+w‖^s ≤ 2^s*(‖z‖^s+‖w‖^s) := by
  rcases le_total ‖z‖ ‖w‖ with h | h
  · calc
      _ ≤ (2*‖w‖)^s := Real.rpow_le_rpow (norm_nonneg _)
        ((norm_add_le z w).trans (by linarith)) hs
      _ = 2^s*‖w‖^s := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)) (by positivity)
  · calc
      _ ≤ (2*‖z‖)^s := Real.rpow_le_rpow (norm_nonneg _)
        ((norm_add_le z w).trans (by linarith)) hs
      _ = 2^s*‖z‖^s := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)) (by positivity)

theorem densityDefect_pointwise_bound {alpha : ℝ} (ha : 0 < alpha)
    (g f : Space → ℂ) (x : Space) :
    |densityDefect alpha g f x| ≤ densityDefectConstant alpha * mixedPower (2+alpha) 1 g f x +
      densityDefectConstant alpha * powerDensity alpha f x := by
  have hs : 0 ≤ 2+alpha := by linarith
  have hp : 0 ≤ 3+alpha := by linarith
  have hd := HartreeEnergy.abs_norm_rpow_sub_norm_rpow_le
    (show 1 ≤ 3+alpha by linarith) (g x+f x) (g x)
  simp only [add_sub_cancel_left, show 3+alpha-1=2+alpha by ring] at hd
  have hab := norm_add_rpow_bound hs (g x) (f x)
  have hfp : ‖f x‖^(2+alpha)*‖f x‖ = ‖f x‖^(3+alpha) := by
    rw [← Real.rpow_add_one' (norm_nonneg _) (by linarith : 2+alpha+1 ≠ 0)]
    congr 1
    ring
  have hn1 := Real.rpow_nonneg (norm_nonneg (g x)) (2+alpha)
  have hn2 := Real.rpow_nonneg (norm_nonneg (f x)) (3+alpha)
  have hn3 := Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2+alpha)
  have h := (abs_sub (‖g x+f x‖^(3+alpha)-‖g x‖^(3+alpha)) (‖f x‖^(3+alpha))).trans
    (add_le_add hd le_rfl)
  rw [abs_of_nonneg hn2] at h
  have hb : (3+alpha)*(‖g x+f x‖^(2+alpha)+‖g x‖^(2+alpha))*‖f x‖ ≤
      (3+alpha)*(2^(2+alpha)*(‖g x‖^(2+alpha)+‖f x‖^(2+alpha))+‖g x‖^(2+alpha))*‖f x‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add hab le_rfl) hp) (norm_nonneg _)
  have he : (3+alpha)*(2^(2+alpha)*(‖g x‖^(2+alpha)+‖f x‖^(2+alpha))+‖g x‖^(2+alpha))*‖f x‖ =
      (3+alpha)*(2^(2+alpha)+1)*(‖g x‖^(2+alpha)*‖f x‖) +
      (3+alpha)*2^(2+alpha)*‖f x‖^(3+alpha) := by
    rw [← hfp]; ring
  have hmix : 0 ≤ ‖g x‖^(2+alpha)*‖f x‖ := mul_nonneg hn1 (norm_nonneg _)
  have hfinal := h.trans (add_le_add hb le_rfl)
  rw [he] at hfinal
  change |‖g x+f x‖^(3+alpha)-‖g x‖^(3+alpha)-‖f x‖^(3+alpha)| ≤ _ at hfinal
  simp only [densityDefect, powerDensity, Pi.add_apply, mixedPower, Real.rpow_one,
    densityDefectConstant]
  nlinarith

/-- The literal Lq density defect, with q=6/(3+alpha)>1. -/
theorem powerDensity_defect_tendsto_zero {alpha B : ℝ} (ha : 0 < alpha) (ha3 : alpha < 3)
    {g : ℕ → Space → ℂ} {f : Space → ℂ}
    (hg : ∀ n, MemLp (g n) 6 volume) (hf : MemLp f 6 volume)
    (hbound : ∀ n, (eLpNorm (g n) 6 volume).toReal ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => g n x) atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm (densityDefect alpha (g n) f)
      (ENNReal.ofReal (densityExponent alpha)) volume).toReal) atTop (𝓝 0) := by
  let q : ℝ≥0∞ := ENNReal.ofReal (densityExponent alpha)
  let C := densityDefectConstant alpha
  have hC : 0 < C := densityDefectConstant_pos ha
  have hp : 0 < 3+alpha := by linarith
  have hqreal : 1 < densityExponent alpha := by
    unfold densityExponent
    exact (lt_div_iff₀ hp).mpr (by linarith)
  have hq1 : 1 ≤ q := ENNReal.one_le_ofReal.mpr hqreal.le
  have hq0 : q ≠ 0 := (lt_of_lt_of_le (by norm_num) hq1).ne'
  have hqt : q ≠ ∞ := ENNReal.ofReal_ne_top
  have hd (n : ℕ) : MemLp (densityDefect alpha (g n) f) q volume :=
    ((powerDensity_memLp ha ((hg n).add hf)).sub (powerDensity_memLp ha (hg n))).sub
      (powerDensity_memLp ha hf)
  have hfixed : MemLp (powerDensity alpha f) q volume := powerDensity_memLp ha hf
  have hmixed (n : ℕ) : MemLp (mixedPower (2+alpha) 1 (g n) f) q volume := by
    simpa only [show 2+alpha+1=3+alpha by ring, q, densityExponent] using
      mixedPower_memLp (by linarith : 0<2+alpha) (by norm_num : (0:ℝ)<1) (hg n) hf
  have hmt : Tendsto (fun n => (eLpNorm (mixedPower (2+alpha) 1 (g n) f) q volume).toReal)
      atTop (𝓝 0) := by
    simpa only [show 2+alpha+1=3+alpha by ring, q, densityExponent] using
      mixedPower_tendsto_zero (by linarith : 0<2+alpha) (by norm_num : (0:ℝ)<1)
        (by linarith : 2+alpha+1≤6) hg hf hbound hlim
  have hdt : ∀ᵐ x ∂volume, Tendsto (fun n => densityDefect alpha (g n) f x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have ht := (((hx.add_const (f x)).norm.rpow_const (Or.inr hp.le)).sub
      (hx.norm.rpow_const (Or.inr hp.le))).sub_const (‖f x‖^(3+alpha))
    simpa only [densityDefect, powerDensity, Pi.add_apply, zero_add, norm_zero,
      Real.zero_rpow hp.ne', sub_zero, sub_self] using ht
  let H : ℕ → Space → ℝ := fun n x => min |densityDefect alpha (g n) f x| (C*powerDensity alpha f x)
  have hHm (n : ℕ) : AEStronglyMeasurable (H n) volume :=
    ((hd n).aestronglyMeasurable.norm.aemeasurable.min
      (hfixed.aestronglyMeasurable.aemeasurable.const_mul C)).aestronglyMeasurable
  have hHb (n : ℕ) : ∀ᵐ x ∂volume, ‖H n x‖ ≤ ‖C*powerDensity alpha f x‖ := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by dsimp [H,powerDensity]; positivity),
      abs_of_nonneg (by unfold powerDensity; positivity)]
    exact min_le_right _ _
  have hHmem (n : ℕ) : MemLp (H n) q volume := (hfixed.const_mul C).of_le (hHm n) (hHb n)
  have hHt : Tendsto (fun n => eLpNorm (H n) q volume) atTop (𝓝 0) := by
    apply strong_lp_zero_of_ae_dominated hq0 hqt hHm (hfixed.const_mul C) hHb
    filter_upwards [hdt] with x hx
    simpa only [H, abs_zero, min_eq_left (show (0:ℝ) ≤ C*powerDensity alpha f x by
      unfold powerDensity; positivity)] using hx.abs.min (tendsto_const_nhds (x := C*powerDensity alpha f x))
  have hHr : Tendsto (fun n => (eLpNorm (H n) q volume).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal (by simp)).comp hHt
  have hup : Tendsto (fun n => (eLpNorm (H n) q volume).toReal +
      C*(eLpNorm (mixedPower (2+alpha) 1 (g n) f) q volume).toReal) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hHr.add (hmt.const_mul C)
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg) _ hup
  intro n
  have hpt (x : Space) : |densityDefect alpha (g n) f x| ≤
      H n x + C*mixedPower (2+alpha) 1 (g n) f x := by
    have hbnd := densityDefect_pointwise_bound ha (g n) f x
    have hm0 : 0 ≤ C*mixedPower (2+alpha) 1 (g n) f x := by unfold mixedPower; positivity
    dsimp only [H]
    by_cases hh : |densityDefect alpha (g n) f x| ≤ C*powerDensity alpha f x
    · rw [min_eq_left hh]
      exact le_add_of_nonneg_right hm0
    · rw [min_eq_right (le_of_not_ge hh)]
      linarith
  have he : eLpNorm (densityDefect alpha (g n) f) q volume ≤
      eLpNorm (H n) q volume + ENNReal.ofReal C * eLpNorm (mixedPower (2+alpha) 1 (g n) f) q volume := by
    calc
      _ ≤ eLpNorm (fun x => H n x+C*mixedPower (2+alpha) 1 (g n) f x) q volume := by
        apply eLpNorm_mono_ae (hd n).aestronglyMeasurable
        filter_upwards [] with x
        change |densityDefect alpha (g n) f x| ≤ |H n x+C*mixedPower (2+alpha) 1 (g n) f x|
        have hpos : 0 ≤ H n x+C*mixedPower (2+alpha) 1 (g n) f x := by
          dsimp [H,mixedPower,powerDensity]
          positivity
        rw [abs_of_nonneg hpos]
        exact hpt x
      _ ≤ _ := by
        convert (eLpNorm_add_le hq1 (f := H n) (g := C • mixedPower (2+alpha) 1 (g n) f)) using 1
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC.le]
  have hfin : eLpNorm (H n) q volume+ENNReal.ofReal C*eLpNorm (mixedPower (2+alpha) 1 (g n) f) q volume ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨(hHmem n).eLpNorm_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmixed n).eLpNorm_ne_top⟩
  have hr := ENNReal.toReal_mono hfin he
  simpa only [ENNReal.toReal_add (hHmem n).eLpNorm_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmixed n).eLpNorm_ne_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] using hr

#print axioms densityDefect_pointwise_bound
#print axioms powerDensity_defect_tendsto_zero
end HartreeF.NonlocalBL
