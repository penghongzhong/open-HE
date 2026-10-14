import ComplexPowerDifference

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.ForcingContinuity
open ForcingDomain

/-- The exact Holder exponents for the complex local factor. -/
theorem localFactor_holderTriple {α : ℝ} (hα : 0 < α) :
    Real.HolderTriple (6/(1+α)) 6 (energyOuterExponent α) := by
  constructor
  · simp only [energyOuterExponent, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · exact div_pos (by norm_num) (by linarith)
  · norm_num

/-- The actual complex local factor obeys a quantitative L6-to-L^(6/(2+alpha)) bound. -/
theorem localFactor_difference_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u v : Space → ℂ} (hu : MemLp u 6 volume) (hv : MemLp v 6 volume) :
    (eLpNorm (localFactor α u-localFactor α v)
      (ENNReal.ofReal (energyOuterExponent α)) volume).toReal ≤
    (2+α) * ((eLpNorm u 6 volume).toReal^(1+α) +
      (eLpNorm v 6 volume).toReal^(1+α)) *
      (eLpNorm (u-v) 6 volume).toReal := by
  let r : ℝ≥0∞ := ENNReal.ofReal (6/(1+α))
  let q : ℝ≥0∞ := ENNReal.ofReal (energyOuterExponent α)
  let A : Space → ℝ := fun x => ‖u x‖^(1+α)
  let B : Space → ℝ := fun x => ‖v x‖^(1+α)
  let D : Space → ℝ := fun x => ‖u x-v x‖
  have hs : 0 < 1+α := by linarith
  have hp : 0 ≤ 2+α := by linarith
  let : ENNReal.HolderTriple r 6 q := by
    simpa only [ENNReal.ofReal_ofNat] using (localFactor_holderTriple hα).ennrealOfReal
  have hr : 1 ≤ r := by
    apply (ENNReal.one_le_ofReal).mpr
    exact (le_div_iff₀ hs).mpr (by linarith)
  have ha : MemLp A r volume := norm_power_memLp hs (by simpa using hu)
  have hb : MemLp B r volume := norm_power_memLp hs (by simpa using hv)
  have hd : MemLp D 6 volume := (hu.sub hv).norm
  have hh : MemLp (localFactor α u-localFactor α v) q volume :=
    (localFactor_memLp (p := 6) hα (by simpa using hu)).sub
      (localFactor_memLp (p := 6) hα (by simpa using hv))
  have he : eLpNorm (localFactor α u-localFactor α v) q volume ≤
      ENNReal.ofReal (2+α) *
        (eLpNorm A r volume+eLpNorm B r volume)*eLpNorm D 6 volume := by
    calc
      _ ≤ eLpNorm ((2+α) • ((A+B)*D)) q volume := by
        apply eLpNorm_mono_ae hh.aestronglyMeasurable
        filter_upwards [] with x
        have hx := localFactor_pointwise_difference hα u v x
        simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.mul_apply, Pi.add_apply, Real.norm_eq_abs, A, B, D,
          abs_of_nonneg (mul_nonneg (mul_nonneg hp
            (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)))
              (norm_nonneg _)), mul_assoc] using hx.trans (le_abs_self _)
      _ = ENNReal.ofReal (2+α) * eLpNorm ((A+B)*D) q volume := by
        rw [eLpNorm_const_smul]
        congr 1
        rw [Real.enorm_eq_ofReal hp]
      _ ≤ ENNReal.ofReal (2+α) *
          ((eLpNorm A r volume+eLpNorm B r volume)*eLpNorm D 6 volume) := by
        apply mul_le_mul' le_rfl
        exact (eLpNorm_smul_le_mul_eLpNorm (ha.add hb).aestronglyMeasurable
          hd.aestronglyMeasurable).trans (mul_le_mul' (eLpNorm_add_le hr) le_rfl)
      _ = _ := by ring
  have hn : ENNReal.ofReal (2+α) *
      (eLpNorm A r volume+eLpNorm B r volume)*eLpNorm D 6 volume ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨ha.eLpNorm_ne_top,hb.eLpNorm_ne_top⟩))
      hd.eLpNorm_ne_top
  have ht := ENNReal.toReal_mono hn he
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_add ha.eLpNorm_ne_top hb.eLpNorm_ne_top] at ht
  have hA : eLpNorm A r volume = eLpNorm u 6 volume^(1+α) := by
    simpa only [ENNReal.ofReal_ofNat] using norm_power_eLpNorm (p := 6) hs hu.aestronglyMeasurable
  have hB : eLpNorm B r volume = eLpNorm v 6 volume^(1+α) := by
    simpa only [ENNReal.ofReal_ofNat] using norm_power_eLpNorm (p := 6) hs hv.aestronglyMeasurable
  have hD : eLpNorm D 6 volume = eLpNorm (u-v) 6 volume :=
    eLpNorm_norm _ (hu.sub hv).aestronglyMeasurable
  rw [hA,hB,hD,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at ht
  exact ht

/-- Strong local-factor continuity for arbitrary actual complex functions and filters.
No homogeneous-Sobolev, mass, or target-continuity premise is needed here. -/
theorem strong_localFactor_tendsto {ι : Type*} {l : Filter ι} {α : ℝ}
    (hα : 0 < α) (hα3 : α < 3) {u : ι → Space → ℂ} {v : Space → ℂ}
    (hu : ∀ i, MemLp (u i) 6 volume) (hv : MemLp v 6 volume)
    (ht : Tendsto (fun i => (eLpNorm (u i-v) 6 volume).toReal) l (𝓝 0)) :
    Tendsto (fun i => (eLpNorm (localFactor α (u i)-localFactor α v)
      (ENNReal.ofReal (energyOuterExponent α)) volume).toReal) l (𝓝 0) := by
  have htLp : Tendsto (fun i => (hu i).toLp (u i)) l (𝓝 (hv.toLp v)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [DotH1Topology.toLp_distance, Pi.sub_def] using ht
  have hnorm : Tendsto (fun i => (eLpNorm (u i) 6 volume).toReal)
      l (𝓝 (eLpNorm v 6 volume).toReal) := by
    simpa only [Lp.norm_toLp] using htLp.norm
  have hpow := hnorm.rpow_const (Or.inr (show 0 ≤ 1+α by linarith))
  have hb : Tendsto (fun i => (2+α)*((eLpNorm (u i) 6 volume).toReal^(1+α)+
      (eLpNorm v 6 volume).toReal^(1+α))*(eLpNorm (u i-v) 6 volume).toReal) l (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds.mul (hpow.add tendsto_const_nhds)).mul ht)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun i => localFactor_difference_bound hα hα3 (hu i) hv) hb

#print axioms strong_localFactor_tendsto
#print axioms localFactor_holderTriple
#print axioms localFactor_difference_bound
end HartreeF.ForcingContinuity
