import FEnergyCriticalTimeConsumer
import FFourInputLocalization

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace HartreeF.ActualStrichartz
open MeasureTheory Filter SobolevStretch StationarySelfTest TimeHolder EnergySpace
open scoped ENNReal NNReal

/-- Reconstruct a real projected gradient from three actual complex fields. -/
def jointProjection (L : ℂ →L[ℝ] ℝ) (d : Fin 3 → ℝ → Space → ℂ)
    (t : ℝ) (x : Space) : Space := ∑ j : Fin 3, L (d j t x) • coordinate j

theorem jointProjection_stronglyMeasurable (L : ℂ →L[ℝ] ℝ)
    (d : Fin 3 → ℝ → Space → ℂ)
    (hd : ∀ j, StronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2)) :
    StronglyMeasurable (fun z : ℝ × Space => jointProjection L d z.1 z.2) := by
  unfold jointProjection
  simpa only [Finset.sum_fn] using Finset.stronglyMeasurable_sum Finset.univ
    (fun j _ => (L.continuous.comp_stronglyMeasurable (hd j)).smul_const (coordinate j))

theorem jointProjection_mixedNorm_le (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) (d : Fin 3 → ℝ → Space → ℂ)
    (hd : ∀ j, StronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2))
    (q : ℝ≥0∞) (hq : 1 ≤ q) (hqTop : q ≠ ∞) :
    mixedNorm volume volume 10 q (jointProjection L d) ≤
      ∑ j : Fin 3, mixedNorm volume volume 10 q (d j) := by
  have hm := spatial_lp_time_measurable (volume : Measure ℝ) volume q
    (by exact ne_zero_of_lt (lt_of_lt_of_le zero_lt_one hq)) hqTop
    (jointProjection L d) (jointProjection_stronglyMeasurable L d hd).aestronglyMeasurable
  have hs (t : ℝ) : eLpNorm (jointProjection L d t) q volume ≤
      ∑ j : Fin 3, eLpNorm (d j t) q volume := by
    calc
      _ ≤ ∑ j : Fin 3, eLpNorm (fun x => L (d j t x) • coordinate j) q volume := by
        change eLpNorm (fun x => ∑ j : Fin 3, L (d j t x) • coordinate j) q volume ≤ _
        simpa only [Finset.sum_fn] using
          (eLpNorm_sum_le (μ := (volume : Measure Space))
            (f := fun j : Fin 3 => fun x => L (d j t x) • coordinate j) hq)
      _ ≤ _ := Finset.sum_le_sum fun j _ => by
        apply eLpNorm_mono
          (((L.continuous.comp_stronglyMeasurable
            ((hd j).comp_measurable (measurable_const.prodMk measurable_id))).smul_const
              (coordinate j)).aestronglyMeasurable)
        intro x
        simpa [norm_smul, coordinate] using hL (d j t x)
  unfold mixedNorm
  calc
    _ ≤ eLpNorm (fun t => ∑ j : Fin 3, eLpNorm (d j t) q volume) 10 volume :=
      eLpNorm_mono_enorm hm (fun t => by simpa only [enorm_eq_self] using hs t)
    _ ≤ _ := by simpa only [Finset.sum_fn] using
      (eLpNorm_sum_le (μ := (volume : Measure ℝ))
        (f := fun j : Fin 3 => fun t => eLpNorm (d j t) q volume)
        (by norm_num : (1 : ℝ≥0∞) ≤ 10))

theorem jointProjection_mixedNorm_finite (L : ℂ →L[ℝ] ℝ)
    (hL : ∀ z, ‖L z‖ ≤ ‖z‖) (d : Fin 3 → ℝ → Space → ℂ)
    (hd : ∀ j, StronglyMeasurable (fun z : ℝ × Space => d j z.1 z.2))
    (q : ℝ≥0∞) (hq : 1 ≤ q) (hqTop : q ≠ ∞)
    (hfin : ∀ j, mixedNorm volume volume 10 q (d j) ≠ ∞) :
    mixedNorm volume volume 10 q (jointProjection L d) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (jointProjection_mixedNorm_le L hL d hd q hq hqTop)
  exact ENNReal.sum_ne_top.mpr (fun j _ => hfin j)

/-- The three supplied fields are representatives of the already existing state
coordinates. Projection compatibility is a theorem, with no PDE premise. -/
theorem jointProjection_energy_ae (L : ℂ →L[ℝ] ℝ)
    (g : ℝ → EnergyState) (d : Fin 3 → ℝ → Space → ℂ)
    (heq : ∀ j, ∀ᵐ t ∂(volume : Measure ℝ), d j t =ᵐ[volume] energyGradient j (g t)) :
    ∀ᵐ t ∂(volume : Measure ℝ), jointProjection L d t =ᵐ[volume]
      energyProjectedGradient L (g t) := by
  filter_upwards [eventually_all.mpr heq] with t ht
  filter_upwards [eventually_all.mpr ht] with x hx
  exact Finset.sum_congr rfl (fun j _ => by rw [show d j t x = energyGradient j (g t) x from hx j])

theorem energyProjected_mixedNorm_eq (L : ℂ →L[ℝ] ℝ)
    (g : ℝ → EnergyState) (d : Fin 3 → ℝ → Space → ℂ)
    (heq : ∀ j, ∀ᵐ t ∂(volume : Measure ℝ), d j t =ᵐ[volume] energyGradient j (g t))
    (p q : ℝ≥0∞) :
    mixedNorm volume volume p q (fun t => energyProjectedGradient L (g t)) =
      mixedNorm volume volume p q (jointProjection L d) := by
  apply eLpNorm_congr_ae
  filter_upwards [jointProjection_energy_ae L g d heq] with t ht
  exact eLpNorm_congr_ae ht.symm

end HartreeF.ActualStrichartz
