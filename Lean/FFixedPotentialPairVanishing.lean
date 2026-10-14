import FPowerDensityBrezisLieb
import HartreeBilinearDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.NonlocalBL
open ForcingDomain SharpOrdinary EnergyContinuity

/-- Dual Lq testing of the power density from actual bounded L6 and a.e. convergence. -/
theorem fixedPotential_pair_tendsto_zero {alpha B : ℝ} (ha : 0<alpha) (ha3 : alpha<3)
    {g : ℕ → Space → ℂ} {h : Space → ℝ}
    (hg : ∀ n, MemLp (g n) 6 volume)
    (hh : MemLp h (ENNReal.ofReal (potentialExponent alpha)) volume)
    (hbound : ∀ n, (eLpNorm (g n) 6 volume).toReal ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => g n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, powerDensity alpha (g n) x*h x) atTop (𝓝 0) := by
  have hb : 0<3-alpha := by linarith
  have hp : 0<3+alpha := by linarith
  let k : Space → ℝ := fun x => ‖h x‖^(1/(3-alpha))
  have hk : MemLp k 6 volume := by
    have hm := hh.norm_rpow_div (ENNReal.ofReal (1/(3-alpha)))
    have he : potentialExponent alpha / (1/(3-alpha)) = 6 := by
      unfold potentialExponent
      field_simp
    simpa only [ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤1/(3-alpha)),
      ← ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ)<1/(3-alpha)), he,
      ENNReal.ofReal_ofNat, k] using hm
  have hkpow (x : Space) : ‖k x‖^(3-alpha)=‖h x‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [k]; positivity)]
    dsimp only [k]
    rw [← Real.rpow_mul (norm_nonneg _), div_mul_cancel₀ _ hb.ne', Real.rpow_one]
  have ht := mixedPower_tendsto_zero hp hb (by linarith : 3+alpha+(3-alpha)≤6)
    hg hk hbound hlim
  have hmix (n : ℕ) : MemLp (mixedPower (3+alpha) (3-alpha) (g n) k) 1 volume := by
    simpa only [show 3+alpha+(3-alpha)=6 by ring, div_self (by norm_num : (6:ℝ)≠0),
      ENNReal.ofReal_one] using mixedPower_memLp hp hb (hg n) hk
  have hmzero : Tendsto (fun n => (eLpNorm (mixedPower (3+alpha) (3-alpha) (g n) k) 1 volume).toReal)
      atTop (𝓝 0) := by
    simpa only [show 3+alpha+(3-alpha)=6 by ring, div_self (by norm_num : (6:ℝ)≠0),
      ENNReal.ofReal_one] using ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ hmzero
  intro n
  calc
    ‖∫ x, powerDensity alpha (g n) x*h x‖ ≤ ∫ x, ‖powerDensity alpha (g n) x*h x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖mixedPower (3+alpha) (3-alpha) (g n) k x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mixedPower, hkpow]
      simp only [powerDensity, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), abs_abs]
    _ = _ := by rw [integral_norm_eq_lintegral_enorm (hmix n).aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm (hmix n).aestronglyMeasurable]

/-- Symmetry uses the actual even Riesz kernel and the measure-preserving swap. -/
theorem bilinearRieszPair_integral_symm (alpha : ℝ) (f g : Space → ℝ) :
    (∫ z, bilinearRieszPair alpha f g z ∂volume.prod volume) =
      ∫ z, bilinearRieszPair alpha g f z ∂volume.prod volume := by
  rw [← integral_prod_swap (bilinearRieszPair alpha g f)]
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp only [bilinearRieszPair, rieszKernel, Prod.swap]
  rw [norm_sub_rev z.2 z.1]
  ring

/-- Mixed pair integral is an honest fixed-potential pairing, justified by sharp HLS Fubini. -/
theorem bilinearRieszPair_density_integral {alpha : ℝ} (hH : SharpOrdinaryHLS alpha)
    {f g : Space → ℂ} (hf : MemLp f 6 volume) (hg : MemLp g 6 volume) :
    (∫ z, bilinearRieszPair alpha (powerDensity alpha g) (powerDensity alpha f) z ∂volume.prod volume) =
      ∫ x, powerDensity alpha g x*potential alpha (HeatRiesz.standardRieszConstant alpha) f x := by
  rw [integral_prod _ (hH.bound _ _ (powerDensity_memLp hH.order_pos hg)
    (powerDensity_memLp hH.order_pos hf)).1]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [bilinearRieszPair]
  unfold potential
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- The cross Hartree interaction vanishes; no weak-density hypothesis is assumed. -/
theorem bilinearRieszPair_density_tendsto_zero {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {g : ℕ → Space → ℂ} {f : Space → ℂ}
    (hg : ∀ n, MemLp (g n) 6 volume) (hf : MemLp f 6 volume)
    (hbound : ∀ n, (eLpNorm (g n) 6 volume).toReal ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => g n x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, bilinearRieszPair alpha (powerDensity alpha (g n))
      (powerDensity alpha f) z ∂volume.prod volume) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := potential_domain_bound hOrd
  simpa only [bilinearRieszPair_density_integral hH hf (hg _)] using
    fixedPotential_pair_tendsto_zero hH.order_pos hH.order_lt_three hg (hC f hf).2.1 hbound hlim

#print axioms fixedPotential_pair_tendsto_zero
#print axioms bilinearRieszPair_integral_symm
#print axioms bilinearRieszPair_density_integral
#print axioms bilinearRieszPair_density_tendsto_zero
end HartreeF.NonlocalBL
