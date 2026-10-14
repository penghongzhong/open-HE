import DominatedLpConvergence
import PowerDensityDifference
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The actual mixed-power vanishing estimate needed twice in nonlocal
Brezis–Lieb: in its density defect and in its fixed-potential cross term. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.NonlocalBL
open ForcingDomain WeakHartreeChain

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

def mixedPower (a b : ℝ) (f : Space → E) (g : Space → F) (x : Space) : ℝ :=
  ‖f x‖^a * ‖g x‖^b

theorem normPower_memLp {s : ℝ} (hs : 0 < s) {f : Space → E}
    (hf : MemLp f 6 volume) :
    MemLp (fun x => ‖f x‖^s) (ENNReal.ofReal (6/s)) volume := by
  simpa only [ENNReal.toReal_ofReal hs.le, ENNReal.ofReal_div_of_pos hs,
    ENNReal.ofReal_ofNat] using hf.norm_rpow_div (ENNReal.ofReal s)

theorem normPower_eLpNorm {s : ℝ} (hs : 0 < s) {f : Space → E}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => ‖f x‖^s) (ENNReal.ofReal (6/s)) volume =
      eLpNorm f 6 volume ^ s := by
  rw [eLpNorm_norm_rpow f hf hs, ENNReal.ofReal_div_of_pos hs,
    ENNReal.div_mul_cancel (by simpa using hs) ENNReal.ofReal_ne_top]
  norm_num

theorem mixedPower_memLp {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {f : Space → E} {g : Space → F} (hf : MemLp f 6 volume) (hg : MemLp g 6 volume) :
    MemLp (mixedPower a b f g) (ENNReal.ofReal (6/(a+b))) volume := by
  have ht : Real.HolderTriple (6/a) (6/b) (6/(a+b)) := by
    constructor
    · simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
    · positivity
    · positivity
  let : ENNReal.HolderTriple (ENNReal.ofReal (6/a)) (ENNReal.ofReal (6/b))
      (ENNReal.ofReal (6/(a+b))) := ht.ennrealOfReal
  exact (normPower_memLp ha hf).mul (normPower_memLp hb hg)

/-- A ratio cutoff gives a genuinely dominated part and a uniformly small Lq tail. -/
theorem mixedPower_ratio_bound {a b M : ℝ} (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (z : E) (w : F) :
    ‖z‖^a * ‖w‖^b ≤
      min (‖z‖^a * ‖w‖^b) (M^a * ‖w‖^(a+b)) + M^(-b) * ‖z‖^(a+b) := by
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have htail : 0 ≤ M^(-b) * ‖z‖^(a+b) := by positivity
  by_cases h : ‖z‖ ≤ M * ‖w‖
  · have hnear : ‖z‖^a * ‖w‖^b ≤ M^a * ‖w‖^(a+b) := by
      calc
        _ ≤ (M * ‖w‖)^a * ‖w‖^b :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hz h ha.le) (Real.rpow_nonneg hw b)
        _ = _ := by rw [Real.mul_rpow hM.le hw, mul_assoc,
          ← Real.rpow_add_of_nonneg hw ha.le hb.le]
    rw [min_eq_left hnear]
    exact le_add_of_nonneg_right htail
  · have hwle : ‖w‖ ≤ M⁻¹ * ‖z‖ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hM]
      simpa only [mul_comm] using le_of_not_ge h
    have hfar : ‖z‖^a * ‖w‖^b ≤ M^(-b) * ‖z‖^(a+b) := by
      calc
        _ ≤ ‖z‖^a * (M⁻¹ * ‖z‖)^b :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hw hwle hb.le) (Real.rpow_nonneg hz a)
        _ = _ := by
          rw [Real.mul_rpow (inv_pos.mpr hM).le hz, ← Real.rpow_neg_eq_inv_rpow,
            Real.rpow_add_of_nonneg hz ha.le hb.le]
          ring
    exact hfar.trans (le_add_of_nonneg_left (by positivity))

/-- No strong L6 convergence is assumed. Both powers have strictly positive shares. -/
theorem mixedPower_tendsto_zero {a b B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a+b ≤ 6) {f : ℕ → Space → E} {g : Space → F}
    (hf : ∀ n, MemLp (f n) 6 volume) (hg : MemLp g 6 volume)
    (hbound : ∀ n, (eLpNorm (f n) 6 volume).toReal ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => (eLpNorm (mixedPower a b (f n) g)
      (ENNReal.ofReal (6/(a+b))) volume).toReal) atTop (𝓝 0) := by
  let q : ℝ≥0∞ := ENNReal.ofReal (6/(a+b))
  have hp : 0 < a+b := add_pos ha hb
  have hq0 : q ≠ 0 := (ENNReal.ofReal_pos.mpr (div_pos (by norm_num) hp)).ne'
  have hqt : q ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1 : 1 ≤ q := ENNReal.one_le_ofReal.mpr ((le_div_iff₀ hp).mpr (by simpa using hab))
  have hprod (n : ℕ) : MemLp (mixedPower a b (f n) g) q volume := mixedPower_memLp ha hb (hf n) hg
  have hpowg : MemLp (fun x => ‖g x‖^(a+b)) q volume := normPower_memLp hp hg
  have hpowf (n : ℕ) : MemLp (fun x => ‖f n x‖^(a+b)) q volume := normPower_memLp hp (hf n)
  have hpt : ∀ᵐ x ∂volume, Tendsto (fun n => mixedPower a b (f n) g x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have ht := (hx.norm.rpow_const (Or.inr ha.le)).mul_const (‖g x‖^b)
    simpa only [mixedPower, norm_zero, Real.zero_rpow ha.ne', zero_mul] using ht
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Filter.Eventually.of_forall (fun n => hc.trans_le ENNReal.toReal_nonneg)
  · intro eps heps
    have htail : Tendsto (fun M : ℝ => M^(-b) * B^(a+b)) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_rpow_neg_atTop hb).mul_const (B^(a+b))
    obtain ⟨M,hM1,hMeps⟩ := ((eventually_ge_atTop (1:ℝ)).and
      (htail.eventually (gt_mem_nhds (half_pos heps)))).exists
    have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM1
    let H : ℕ → Space → ℝ := fun n x => min (mixedPower a b (f n) g x) (M^a * ‖g x‖^(a+b))
    have hHmeas (n : ℕ) : AEStronglyMeasurable (H n) volume :=
      ((hprod n).aestronglyMeasurable.aemeasurable.min
        (hpowg.aestronglyMeasurable.aemeasurable.const_mul (M^a))).aestronglyMeasurable
    have hHbound (n : ℕ) : ∀ᵐ x ∂volume, ‖H n x‖ ≤ ‖M^a * ‖g x‖^(a+b)‖ := by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by dsimp [H,mixedPower]; positivity),
        abs_of_nonneg (by positivity)]
      exact min_le_right _ _
    have hHmem (n : ℕ) : MemLp (H n) q volume :=
      (hpowg.const_mul (M^a)).of_le (hHmeas n) (hHbound n)
    have hHt : Tendsto (fun n => eLpNorm (H n) q volume) atTop (𝓝 0) := by
      apply strong_lp_zero_of_ae_dominated hq0 hqt hHmeas (hpowg.const_mul (M^a)) hHbound
      filter_upwards [hpt] with x hx
      simpa only [H, min_eq_left (show (0:ℝ) ≤ M^a * ‖g x‖^(a+b) by positivity)] using
        hx.min (tendsto_const_nhds (x := M^a * ‖g x‖^(a+b)))
    have hHreal : Tendsto (fun n => (eLpNorm (H n) q volume).toReal) atTop (𝓝 0) := by
      exact (ENNReal.tendsto_toReal (by simp)).comp hHt
    filter_upwards [hHreal.eventually (gt_mem_nhds (half_pos heps))] with n hn
    have hbnd : eLpNorm (mixedPower a b (f n) g) q volume ≤
        eLpNorm (H n) q volume + ENNReal.ofReal (M^(-b)) *
          eLpNorm (fun x => ‖f n x‖^(a+b)) q volume := by
      calc
        _ ≤ eLpNorm (fun x => H n x + M^(-b) * ‖f n x‖^(a+b)) q volume := by
          apply eLpNorm_mono_ae (hprod n).aestronglyMeasurable
          filter_upwards [] with x
          rw [Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by dsimp [mixedPower]; positivity), abs_of_nonneg (by dsimp [H,mixedPower]; positivity)]
          exact mixedPower_ratio_bound ha hb hM _ _
        _ ≤ _ := by
          convert (eLpNorm_add_le hq1 (f := H n)
            (g := (M^(-b)) • (fun x => ‖f n x‖^(a+b)))) using 1
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg hM.le _)]
    have hfinite : eLpNorm (H n) q volume + ENNReal.ofReal (M^(-b)) *
        eLpNorm (fun x => ‖f n x‖^(a+b)) q volume ≠ ∞ := by
      exact ENNReal.add_ne_top.mpr ⟨(hHmem n).eLpNorm_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hpowf n).eLpNorm_ne_top⟩
    have hr := ENNReal.toReal_mono hfinite hbnd
    rw [ENNReal.toReal_add (hHmem n).eLpNorm_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hpowf n).eLpNorm_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hM.le _)] at hr
    have hpown : (eLpNorm (fun x => ‖f n x‖^(a+b)) q volume).toReal ≤ B^(a+b) := by
      rw [normPower_eLpNorm hp (hf n).aestronglyMeasurable, ← ENNReal.toReal_rpow]
      exact Real.rpow_le_rpow ENNReal.toReal_nonneg (hbound n) hp.le
    have hfinal := hr.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hpown (Real.rpow_nonneg hM.le (-b))))
    linarith

#print axioms mixedPower_ratio_bound
#print axioms mixedPower_tendsto_zero
end HartreeF.NonlocalBL
