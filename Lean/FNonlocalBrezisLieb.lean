import FFixedPotentialPairVanishing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.NonlocalBL
open ForcingDomain SharpOrdinary EnergyContinuity DirectionalCoercivity

theorem real_eLpNorm_add_le {E : Type*} [NormedAddCommGroup E] {q : ℝ≥0∞}
    (hq : 1≤q) {f g : Space → E} (hf : MemLp f q volume) (hg : MemLp g q volume) :
    (eLpNorm (f+g) q volume).toReal ≤ (eLpNorm f q volume).toReal+(eLpNorm g q volume).toReal := by
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top,hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hq (f:=f) (g:=g) (μ:=volume))
  simpa only [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] using hh

theorem powerDensity_real_norm_bound {alpha B : ℝ} (ha : 0<alpha)
    {u : Space → ℂ} (hu : MemLp u 6 volume)
    (hb : (eLpNorm u 6 volume).toReal≤B) :
    (eLpNorm (powerDensity alpha u) (ENNReal.ofReal (densityExponent alpha)) volume).toReal ≤ B^(3+alpha) := by
  rw [powerDensity_eLpNorm ha hu.aestronglyMeasurable, ← ENNReal.toReal_rpow]
  exact Real.rpow_le_rpow ENNReal.toReal_nonneg hb (by linarith)

/-- Expansion of the actual HLS double integral, with every domain supplied. -/
theorem rieszQuadratic_add {alpha : ℝ} (hH : SharpOrdinaryHLS alpha) {f g : Space → ℝ}
    (hf : MemLp f (ENNReal.ofReal (densityExponent alpha)) volume)
    (hg : MemLp g (ENNReal.ofReal (densityExponent alpha)) volume) :
    rieszQuadratic alpha (f+g)-rieszQuadratic alpha f-rieszQuadratic alpha g =
      (∫ z, bilinearRieszPair alpha f g z ∂volume.prod volume)+
      ∫ z, bilinearRieszPair alpha g f z ∂volume.prod volume := by
  have hsum := (hH.bound (f+g) (f+g) (hf.add hg) (hf.add hg)).1
  have hff := (hH.bound f f hf hf).1
  have hgg := (hH.bound g g hg hg).1
  have hfg := (hH.bound f g hf hg).1
  have hgf := (hH.bound g f hg hf).1
  unfold rieszQuadratic
  rw [← integral_sub hsum hff]
  rw [← integral_sub (f := fun z => bilinearRieszPair alpha (f+g) (f+g) z-
    bilinearRieszPair alpha f f z) (hsum.sub hff) hgg, ← integral_add hfg hgf]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [bilinearRieszPair, Pi.add_apply]
  ring

/-- Actual nonlocal Brezis–Lieb at the critical Hartree exponent.
Only uniform L6 control and a.e. convergence of the remainder to zero are used. -/
theorem interaction_brezis_lieb_remainder {alpha B : ℝ}
    (hH : SharpOrdinaryHLS alpha)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    {g : ℕ → Space → ℂ} {f : Space → ℂ}
    (hg : ∀ n, MemLp (g n) 6 volume) (hf : MemLp f 6 volume)
    (hbound : ∀ n, (eLpNorm (g n) 6 volume).toReal ≤ B)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => g n x) atTop (𝓝 0)) :
    Tendsto (fun n => interaction alpha (g n+f)-interaction alpha (g n)-interaction alpha f)
      atTop (𝓝 0) := by
  let q := ENNReal.ofReal (densityExponent alpha)
  let F := (eLpNorm f 6 volume).toReal
  let K := (B+F)^(3+alpha)+(B^(3+alpha)+F^(3+alpha))
  have ha := hH.order_pos
  have ha3 := hH.order_lt_three
  have hp : 0<3+alpha := by linarith
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr ((lt_div_iff₀ hp).mpr (by linarith)).le
  have hD (n : ℕ) : MemLp (powerDensity alpha (g n+f)) q volume :=
    powerDensity_memLp ha ((hg n).add hf)
  have hR (n : ℕ) : MemLp (powerDensity alpha (g n)) q volume := powerDensity_memLp ha (hg n)
  have hF : MemLp (powerDensity alpha f) q volume := powerDensity_memLp ha hf
  have hS (n : ℕ) : MemLp (powerDensity alpha (g n)+powerDensity alpha f) q volume := (hR n).add hF
  have hDb (n : ℕ) : (eLpNorm (powerDensity alpha (g n+f)) q volume).toReal ≤ (B+F)^(3+alpha) :=
    powerDensity_real_norm_bound ha ((hg n).add hf)
      ((real_eLpNorm_add_le (by norm_num) (hg n) hf).trans (add_le_add (hbound n) le_rfl))
  have hSb (n : ℕ) : (eLpNorm (powerDensity alpha (g n)+powerDensity alpha f) q volume).toReal ≤
      B^(3+alpha)+F^(3+alpha) :=
    (real_eLpNorm_add_le hq (hR n) hF).trans (add_le_add
      (powerDensity_real_norm_bound ha (hg n) (hbound n))
      (powerDensity_real_norm_bound ha hf le_rfl))
  have hd := powerDensity_defect_tendsto_zero ha ha3 hg hf hbound hlim
  have heq (n : ℕ) : powerDensity alpha (g n+f)-(powerDensity alpha (g n)+powerDensity alpha f) =
      densityDefect alpha (g n) f := by
    funext x
    dsimp only [Pi.sub_apply, Pi.add_apply, densityDefect]
    ring
  have hQ : Tendsto (fun n => rieszQuadratic alpha (powerDensity alpha (g n+f))-
      rieszQuadratic alpha (powerDensity alpha (g n)+powerDensity alpha f)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hup : Tendsto (fun n => sharpHLSConstant alpha *
        (eLpNorm (densityDefect alpha (g n) f) q volume).toReal*K) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using (hd.const_mul (sharpHLSConstant alpha)).mul_const K
    apply squeeze_zero (fun n => norm_nonneg _) _ hup
    intro n
    rw [Real.norm_eq_abs]
    have hbnd := rieszQuadratic_difference_bound hH (hD n) (hS n)
    rw [heq] at hbnd
    refine hbnd.trans (mul_le_mul_of_nonneg_left (add_le_add (hDb n) (hSb n)) ?_)
    exact mul_nonneg (sharpHLSConstant_pos ha ha3).le ENNReal.toReal_nonneg
  have hc := bilinearRieszPair_density_tendsto_zero hH hOrd hg hf hbound hlim
  have hs : Tendsto (fun n => rieszQuadratic alpha (powerDensity alpha (g n)+powerDensity alpha f)-
      rieszQuadratic alpha (powerDensity alpha (g n))-rieszQuadratic alpha (powerDensity alpha f))
      atTop (𝓝 0) := by
    have hh : Tendsto (fun n =>
        (∫ z, bilinearRieszPair alpha (powerDensity alpha (g n)) (powerDensity alpha f) z ∂volume.prod volume)+
        ∫ z, bilinearRieszPair alpha (powerDensity alpha f) (powerDensity alpha (g n)) z ∂volume.prod volume)
        atTop (𝓝 0) := by
      simp_rw [bilinearRieszPair_integral_symm alpha (powerDensity alpha f)]
      simpa only [add_zero] using hc.add hc
    simpa only [rieszQuadratic_add hH (hR _) hF] using hh
  have ht := hQ.add hs
  have he : (fun n => interaction alpha (g n+f)-interaction alpha (g n)-interaction alpha f) =
      (fun n => (rieszQuadratic alpha (powerDensity alpha (g n+f))-
        rieszQuadratic alpha (powerDensity alpha (g n)+powerDensity alpha f))+
        (rieszQuadratic alpha (powerDensity alpha (g n)+powerDensity alpha f)-
          rieszQuadratic alpha (powerDensity alpha (g n))-rieszQuadratic alpha (powerDensity alpha f))) := by
    funext n
    rw [interaction_eq_rieszQuadratic hOrd ((hg n).add hf),
      interaction_eq_rieszQuadratic hOrd (hg n), interaction_eq_rieszQuadratic hOrd hf]
    ring
  rw [he]
  simpa only [add_zero] using ht

#print axioms rieszQuadratic_add
#print axioms interaction_brezis_lieb_remainder
end HartreeF.NonlocalBL
