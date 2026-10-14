import PowerDensityDifference

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace HartreeF.ForcingContinuity
open ForcingDomain

/-- Actual convolution subtraction is justified on the two supplied Bochner L1 domains. -/
theorem rieszConvolution_sub_ae {α c : ℝ} {f g : Space → ℝ}
    (hf : ∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y)*f y) volume)
    (hg : ∀ᵐ x ∂volume, Integrable (fun y => rieszKernel α c (x-y)*g y) volume) :
    rieszConvolution α c (f-g) =ᵐ[volume]
      rieszConvolution α c f-rieszConvolution α c g := by
  filter_upwards [hf,hg] with x hfx hgx
  change (∫ y, rieszKernel α c (x-y)*(f y-g y)) =
    (∫ y, rieszKernel α c (x-y)*f y) - ∫ y, rieszKernel α c (x-y)*g y
  simp_rw [mul_sub]
  exact integral_sub hfx hgx

/-- Ordinary strong HLS yields finite actual-potential difference bounds.
All subtraction equalities use AE absolute-convolution domains first. -/
theorem potential_difference_domain_bound {α c : ℝ} (hH : OrdinaryHLS α c) :
    ∃ C : ℝ≥0, ∀ u v : Space → ℂ, MemLp u 6 volume → MemLp v 6 volume →
      MemLp (potential α c u-potential α c v)
        (ENNReal.ofReal (potentialExponent α)) volume ∧
      (eLpNorm (potential α c u-potential α c v)
        (ENNReal.ofReal (potentialExponent α)) volume).toReal ≤
        (C : ℝ)*(eLpNorm (powerDensity α u-powerDensity α v)
          (ENNReal.ofReal (densityExponent α)) volume).toReal ∧
      (eLpNorm (potential α c v) (ENNReal.ofReal (potentialExponent α)) volume).toReal ≤
        (C : ℝ)*(eLpNorm v 6 volume).toReal^(3+α) := by
  obtain ⟨hq1,hqα,hr,hrel⟩ := energyHLS_range hH.order_pos hH.order_lt_three
  obtain ⟨C,hC⟩ := hH.strong_bound _ _ hq1 hqα hr hrel
  refine ⟨C, fun u v hu hv => ?_⟩
  have hdu := powerDensity_memLp hH.order_pos hu
  have hdv := powerDensity_memLp hH.order_pos hv
  obtain ⟨hiu,hpu,_hbu⟩ := hC (powerDensity α u) hdu
  obtain ⟨hiv,hpv,hbv⟩ := hC (powerDensity α v) hdv
  obtain ⟨_hid,hpd,hbd⟩ := hC (powerDensity α u-powerDensity α v) (hdu.sub hdv)
  have he := rieszConvolution_sub_ae hiu hiv
  have hnorm : eLpNorm (potential α c u-potential α c v)
      (ENNReal.ofReal (potentialExponent α)) volume =
      eLpNorm (rieszConvolution α c (powerDensity α u-powerDensity α v))
        (ENNReal.ofReal (potentialExponent α)) volume := eLpNorm_congr_ae he.symm
  refine ⟨hpu.sub hpv, ?_, ?_⟩
  · rw [hnorm]
    have hn : (C : ℝ≥0∞)*eLpNorm (powerDensity α u-powerDensity α v)
        (ENNReal.ofReal (densityExponent α)) volume ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (hdu.sub hdv).eLpNorm_ne_top
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using ENNReal.toReal_mono hn hbd
  · rw [powerDensity_eLpNorm hH.order_pos hv.aestronglyMeasurable] at hbv
    have hn : (C : ℝ≥0∞)*eLpNorm v 6 volume^(3+α) ≠ ∞ := by
      apply ENNReal.mul_ne_top ENNReal.coe_ne_top
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith [hH.order_pos]) hv.eLpNorm_ne_top
    simpa only [potential_eq_convolution, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_rpow] using
      ENNReal.toReal_mono hn hbv

/-- Strong continuity of the literal integral potential, from strong L6 alone. -/
theorem strong_potential_tendsto {ι : Type*} {l : Filter ι} {α c : ℝ}
    (hH : OrdinaryHLS α c) {u : ι → Space → ℂ} {v : Space → ℂ}
    (hu : ∀ i, MemLp (u i) 6 volume) (hv : MemLp v 6 volume)
    (ht : Tendsto (fun i => (eLpNorm (u i-v) 6 volume).toReal) l (𝓝 0)) :
    Tendsto (fun i => (eLpNorm (potential α c (u i)-potential α c v)
      (ENNReal.ofReal (potentialExponent α)) volume).toReal) l (𝓝 0) := by
  obtain ⟨C,hC⟩ := potential_difference_domain_bound hH
  have htd := EnergyContinuity.strong_powerDensity_tendsto
    hH.order_pos hH.order_lt_three hu hv ht
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun i => (hC (u i) v (hu i) hv).2.1)
  simpa only [mul_zero] using tendsto_const_nhds.mul htd

#print axioms rieszConvolution_sub_ae
#print axioms potential_difference_domain_bound
#print axioms strong_potential_tendsto
end HartreeF.ForcingContinuity
