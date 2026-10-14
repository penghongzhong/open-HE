import CriticalSaturation

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.CriticalSobolevBridge
open SobolevStretch StationarySelfTest WeakHartreeChain WeakHartreeProduct

theorem critical_holder_gradient_bound
    {f : Space → ℝ} {G U V : Space → Space}
    (hf : MemLp f 6 volume) (hG : MemLp G 2 volume)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hpoint : ∀ x, ‖G x‖ ≤ (5/3)*‖f x‖^(2/5 : ℝ)*(‖U x‖+‖V x‖)) :
    (eLpNorm G 2 volume).toReal ≤
      (5/3)*(eLpNorm f 6 volume).toReal^(2/5 : ℝ)*
        ((eLpNorm U (ENNReal.ofReal (30/13 : ℝ)) volume).toReal+
         (eLpNorm V (ENNReal.ofReal (30/13 : ℝ)) volume).toReal) := by
  let a : Space → ℝ := fun x => ‖f x‖^(2/5 : ℝ)
  let w : Space → ℝ := fun x => ‖U x‖+‖V x‖
  have ha : MemLp a (ENNReal.ofReal (15 : ℝ)) volume := by
    have hq : (6:ℝ≥0∞) / ENNReal.ofReal (2/5:ℝ) = ENNReal.ofReal (15:ℝ) := by
      rw [show (6:ℝ≥0∞) = ENNReal.ofReal (6:ℝ) by norm_num,
        ← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2/5)]
      norm_num
    simpa only [ENNReal.toReal_ofReal (show (0:ℝ)≤2/5 by norm_num),hq] using
      hf.norm_rpow_div (ENNReal.ofReal (2/5 : ℝ))
  have hw : MemLp w (ENNReal.ofReal (30/13 : ℝ)) volume := hU.norm.add hV.norm
  have ht : Real.HolderTriple 15 (30/13) 2 := by constructor <;> norm_num
  let : ENNReal.HolderTriple (ENNReal.ofReal (15:ℝ)) (ENNReal.ofReal (30/13:ℝ)) 2 := by
    simpa only [ENNReal.ofReal_ofNat] using ht.ennrealOfReal
  have hfirst : eLpNorm G 2 volume ≤ ENNReal.ofReal (5/3:ℝ)*eLpNorm (a • w) 2 volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hG.aestronglyMeasurable
    filter_upwards [] with x
    change ‖G x‖ ≤ (5/3)*|‖f x‖^(2/5:ℝ)*(‖U x‖+‖V x‖)|
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))]
    simpa only [mul_assoc] using hpoint x
  have hsecond : eLpNorm (a • w) 2 volume ≤ eLpNorm a (ENNReal.ofReal 15) volume *
      eLpNorm w (ENNReal.ofReal (30/13:ℝ)) volume := by
    exact eLpNorm_smul_le_mul_eLpNorm ha.aestronglyMeasurable hw.aestronglyMeasurable
  have haEq : eLpNorm a (ENNReal.ofReal 15) volume = eLpNorm f 6 volume ^ (2/5:ℝ) := by
    change eLpNorm (fun x => ‖f x‖^(2/5:ℝ)) (ENNReal.ofReal 15) volume = _
    rw [eLpNorm_norm_rpow f hf.aestronglyMeasurable (by norm_num : (0:ℝ)<2/5)]
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤15)]
    norm_num
  have hwLe : eLpNorm w (ENNReal.ofReal (30/13:ℝ)) volume ≤
      eLpNorm U (ENNReal.ofReal (30/13:ℝ)) volume + eLpNorm V (ENNReal.ofReal (30/13:ℝ)) volume := by
    have hh := eLpNorm_add_le (f := fun x => ‖U x‖) (g := fun x => ‖V x‖)
      (μ := volume) (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal (30/13:ℝ) by norm_num)
    simpa only [w,Pi.add_def,eLpNorm_norm U hU.aestronglyMeasurable,eLpNorm_norm V hV.aestronglyMeasurable] using hh
  have hthird : eLpNorm G 2 volume ≤ ENNReal.ofReal (5/3:ℝ)*
      (eLpNorm a (ENNReal.ofReal 15) volume * eLpNorm w (ENNReal.ofReal (30/13:ℝ)) volume) :=
    hfirst.trans (by gcongr)
  rw [haEq] at hthird
  have hfinal : eLpNorm G 2 volume ≤ ENNReal.ofReal (5/3:ℝ)*
      (eLpNorm f 6 volume ^ (2/5:ℝ) *
        (eLpNorm U (ENNReal.ofReal (30/13:ℝ)) volume +
         eLpNorm V (ENNReal.ofReal (30/13:ℝ)) volume)) := hthird.trans (by gcongr)
  have hfinite : ENNReal.ofReal (5/3:ℝ) *
      (eLpNorm f 6 volume ^ (2/5:ℝ) *
        (eLpNorm U (ENNReal.ofReal (30/13:ℝ)) volume +
         eLpNorm V (ENNReal.ofReal (30/13:ℝ)) volume)) ≠ ∞ := by
    finiteness [hf,hU,hV]
  have hr := ENNReal.toReal_mono hfinite hfinal
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (show (0:ℝ)≤5/3 by norm_num),
    ← ENNReal.toReal_rpow,ENNReal.toReal_add hU.eLpNorm_ne_top hV.eLpNorm_ne_top,mul_assoc] using hr

theorem critical_saturation_gradient_norm_bound {ε : ℝ} (hε : 0 < ε)
    {u : Space → ℂ} {U V : Space → Space} (hu : InDotH1 u U V)
    (hU : MemLp U (ENNReal.ofReal (30/13 : ℝ)) volume)
    (hV : MemLp V (ENNReal.ofReal (30/13 : ℝ)) volume) :
    (eLpNorm (fun x => saturationCoeff (5/3) ε (u x) • densityGradient (5/3) u U V x)
      2 volume).toReal ≤
      (5/3)*(eLpNorm (fun x => saturatedDensity (5/3) ε (u x)) 6 volume).toReal^(2/5 : ℝ)*
        ((eLpNorm U (ENNReal.ofReal (30/13 : ℝ)) volume).toReal+
         (eLpNorm V (ENNReal.ofReal (30/13 : ℝ)) volume).toReal) := by
  have hd := critical_saturation_domains hε hu
  apply critical_holder_gradient_bound hd.1 hd.2 hU hV
  intro x
  simpa only [Real.norm_eq_abs,abs_of_nonneg (saturatedDensity_nonneg hε.le _ _)] using
    critical_saturation_gradient_bound hε.le u U V x

#print axioms critical_holder_gradient_bound
#print axioms critical_saturation_gradient_norm_bound
end HartreeF.CriticalSobolevBridge
