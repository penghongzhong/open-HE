import RealPowerDifference
import HartreeBilinearDifference

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.EnergyContinuity
open ForcingDomain

/-- The exact Holder exponents for the full critical real power. -/
theorem density_holderTriple {α : ℝ} (hα : 0 < α) :
    Real.HolderTriple (6/(2+α)) 6 (densityExponent α) := by
  constructor
  · simp only [densityExponent, div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  · exact div_pos (by norm_num) (by linarith)
  · norm_num

/-- Actual complex densities obey a quantitative L6-to-Lq estimate for every 0<alpha<3. -/
theorem powerDensity_difference_bound {α : ℝ} (hα : 0 < α) (hα3 : α < 3)
    {u v : Space → ℂ} (hu : MemLp u 6 volume) (hv : MemLp v 6 volume) :
    (eLpNorm (powerDensity α u-powerDensity α v)
      (ENNReal.ofReal (densityExponent α)) volume).toReal ≤
    (3+α) * ((eLpNorm u 6 volume).toReal^(2+α) +
      (eLpNorm v 6 volume).toReal^(2+α)) *
      (eLpNorm (u-v) 6 volume).toReal := by
  let r : ℝ≥0∞ := ENNReal.ofReal (6/(2+α))
  let q : ℝ≥0∞ := ENNReal.ofReal (densityExponent α)
  let A : Space → ℝ := fun x => ‖u x‖^(2+α)
  let B : Space → ℝ := fun x => ‖v x‖^(2+α)
  let D : Space → ℝ := fun x => ‖u x-v x‖
  have hs : 0 < 2+α := by linarith
  have hp : 0 ≤ 3+α := by linarith
  let : ENNReal.HolderTriple r 6 q := by
    simpa only [ENNReal.ofReal_ofNat] using (density_holderTriple hα).ennrealOfReal
  have hr : 1 ≤ r := by
    apply (ENNReal.one_le_ofReal).mpr
    exact (le_div_iff₀ hs).mpr (by linarith)
  have ha : MemLp A r volume := norm_power_memLp hs (by simpa using hu)
  have hb : MemLp B r volume := norm_power_memLp hs (by simpa using hv)
  have hd : MemLp D 6 volume := (hu.sub hv).norm
  have hh : MemLp (powerDensity α u-powerDensity α v) q volume :=
    (powerDensity_memLp hα hu).sub (powerDensity_memLp hα hv)
  have he : eLpNorm (powerDensity α u-powerDensity α v) q volume ≤
      ENNReal.ofReal (3+α) *
        (eLpNorm A r volume+eLpNorm B r volume)*eLpNorm D 6 volume := by
    calc
      _ ≤ eLpNorm ((3+α) • ((A+B)*D)) q volume := by
        apply eLpNorm_mono_ae hh.aestronglyMeasurable
        filter_upwards [] with x
        have hx := HartreeEnergy.abs_norm_rpow_sub_norm_rpow_le
          (show 1 ≤ 3+α by linarith) (u x) (v x)
        have he : 3+α-1 = 2+α := by ring
        simpa only [powerDensity, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Pi.mul_apply, Pi.add_apply, Real.norm_eq_abs, A, B, D,
          abs_of_nonneg (mul_nonneg (mul_nonneg hp
            (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)))
              (norm_nonneg _)), he, mul_assoc] using hx.trans (le_abs_self _)
      _ = ENNReal.ofReal (3+α) * eLpNorm ((A+B)*D) q volume := by
        rw [eLpNorm_const_smul]
        congr 1
        rw [Real.enorm_eq_ofReal hp]
      _ ≤ ENNReal.ofReal (3+α) *
          ((eLpNorm A r volume+eLpNorm B r volume)*eLpNorm D 6 volume) := by
        apply mul_le_mul' le_rfl
        exact (eLpNorm_smul_le_mul_eLpNorm (ha.add hb).aestronglyMeasurable
          hd.aestronglyMeasurable).trans (mul_le_mul' (eLpNorm_add_le hr) le_rfl)
      _ = _ := by ring
  have hn : ENNReal.ofReal (3+α) *
      (eLpNorm A r volume+eLpNorm B r volume)*eLpNorm D 6 volume ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨ha.eLpNorm_ne_top,hb.eLpNorm_ne_top⟩))
      hd.eLpNorm_ne_top
  have ht := ENNReal.toReal_mono hn he
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_add ha.eLpNorm_ne_top hb.eLpNorm_ne_top] at ht
  have hA : eLpNorm A r volume = eLpNorm u 6 volume^(2+α) := by
    simpa only [ENNReal.ofReal_ofNat] using norm_power_eLpNorm (p := 6) hs hu.aestronglyMeasurable
  have hB : eLpNorm B r volume = eLpNorm v 6 volume^(2+α) := by
    simpa only [ENNReal.ofReal_ofNat] using norm_power_eLpNorm (p := 6) hs hv.aestronglyMeasurable
  have hD : eLpNorm D 6 volume = eLpNorm (u-v) 6 volume :=
    eLpNorm_norm _ (hu.sub hv).aestronglyMeasurable
  rw [hA,hB,hD,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at ht
  exact ht

/-- Full strong L6-to-Lq continuity for arbitrary actual complex functions and filters.
No homogeneous-Sobolev, mass, or target-continuity premise is needed here. -/
theorem strong_powerDensity_tendsto {ι : Type*} {l : Filter ι} {α : ℝ}
    (hα : 0 < α) (hα3 : α < 3) {u : ι → Space → ℂ} {v : Space → ℂ}
    (hu : ∀ i, MemLp (u i) 6 volume) (hv : MemLp v 6 volume)
    (ht : Tendsto (fun i => (eLpNorm (u i-v) 6 volume).toReal) l (𝓝 0)) :
    Tendsto (fun i => (eLpNorm (powerDensity α (u i)-powerDensity α v)
      (ENNReal.ofReal (densityExponent α)) volume).toReal) l (𝓝 0) := by
  have htLp : Tendsto (fun i => (hu i).toLp (u i)) l (𝓝 (hv.toLp v)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [DotH1Topology.toLp_distance, Pi.sub_def] using ht
  have hnorm : Tendsto (fun i => (eLpNorm (u i) 6 volume).toReal)
      l (𝓝 (eLpNorm v 6 volume).toReal) := by
    simpa only [Lp.norm_toLp] using htLp.norm
  have hpow := hnorm.rpow_const (Or.inr (show 0 ≤ 2+α by linarith))
  have hb : Tendsto (fun i => (3+α)*((eLpNorm (u i) 6 volume).toReal^(2+α)+
      (eLpNorm v 6 volume).toReal^(2+α))*(eLpNorm (u i-v) 6 volume).toReal) l (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds.mul (hpow.add tendsto_const_nhds)).mul ht)
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun i => powerDensity_difference_bound hα hα3 (hu i) hv) hb

#print axioms strong_powerDensity_tendsto
#print axioms density_holderTriple
#print axioms powerDensity_difference_bound
end HartreeF.EnergyContinuity
