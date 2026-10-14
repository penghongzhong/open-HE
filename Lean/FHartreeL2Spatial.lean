import HartreeGradientSingle

/-! Literal Hartree forcing in L²_x from L6_x ∩ L10_x, throughout 0 < α < 3.
The only external input is the already accepted ordinary strong-HLS interface.
No L² hypothesis is imposed on the original function. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal NNReal
namespace HartreeF.ForcingL2
open ForcingDomain GradientMajorants

/-- The exact HLS/Holder allocation has output reciprocal 1/2. -/
theorem forcing_l2_allocation (alpha : ℝ) :
    reciprocalA alpha - alpha / 3 + (2 + alpha) / 10 = 1 / 2 := by
  unfold reciprocalA
  ring

/-- Literal scalar majorant, including the genuine Riesz integral domain. -/
theorem forcing_scalar_l2_bound {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ u : Space → ℂ, MemLp u 6 volume → MemLp u 10 volume →
      RieszDomain alpha c (powerDensity alpha u) ∧
      SpatialBound (fun x => potential alpha c u x * ‖u x‖ ^ (2 + alpha)) (1 / 2)
        ((C : ℝ) * spatialNorm 6 (fun x => ‖u x‖) ^ (2 * alpha) *
          spatialNorm 10 (fun x => ‖u x‖) ^ (5 : ℝ)) := by
  obtain ⟨ha, ha1, _, _⟩ := gradient_hls_ranges hH.order_pos hH.order_lt_three
  obtain ⟨C, hC⟩ := convolution_bound hH ha ha1
  refine ⟨C, fun u hu6 hu10 => ?_⟩
  obtain ⟨hd, hp⟩ := hC _ _ (first_density_bound hH.order_pos hH.order_lt_three
    (fun x => norm_nonneg (u x)) hu6.norm hu10.norm)
  have ho := spacetime_power_bound (fun x => norm_nonneg (u x)) hu10.norm
    (show 0 < 2 + alpha by linarith [hH.order_pos])
  refine ⟨hd, ?_⟩
  convert hp.mul ho using 1
  · rfl
  · exact (forcing_l2_allocation alpha).symm
  · symm
    calc
      _ = (C : ℝ) * spatialNorm 6 (fun x => ‖u x‖) ^ (2 * alpha) *
          (spatialNorm 10 (fun x => ‖u x‖) ^ (3 - alpha) *
            spatialNorm 10 (fun x => ‖u x‖) ^ (2 + alpha)) := by ring
      _ = _ := by
        rw [← Real.rpow_add' (spatialNorm_nonneg 10 (fun x => ‖u x‖))
          (show 3 - alpha + (2 + alpha) ≠ 0 by ring_nf; norm_num)]
        congr 2
        ring

/-- Actual complex N(u), with both L² membership and the E^(2α) S^5 bound. -/
theorem forcing_l2_spatial_bound {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀ u : Space → ℂ, MemLp u 6 volume → MemLp u 10 volume →
      MemLp (forcing alpha c u) 2 volume ∧
      (eLpNorm (forcing alpha c u) 2 volume).toReal ≤
        (C : ℝ) * (eLpNorm u 6 volume).toReal ^ (2 * alpha) *
          (eLpNorm u 10 volume).toReal ^ (5 : ℝ) := by
  obtain ⟨C, hC⟩ := forcing_scalar_l2_bound hH
  obtain ⟨C0, hC0⟩ := forcing_energy_domain_bound hH
  refine ⟨C, fun u hu6 hu10 => ?_⟩
  have hb := (hC u hu6 hu10).2
  have hf := (hC0 u hu6).1.aestronglyMeasurable
  have hm : MemLp (fun x => potential alpha c u x * ‖u x‖ ^ (2 + alpha)) 2 volume := by
    simpa using hb.memLp
  have he : ∀ x, ‖forcing alpha c u x‖ =
      ‖potential alpha c u x * ‖u x‖ ^ (2 + alpha)‖ := by
    intro x
    change ‖potential alpha c u x • localFactor alpha u x‖ = _
    simp only [norm_smul, norm_localFactor hH.order_pos,
      norm_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hn : eLpNorm (forcing alpha c u) 2 volume =
      eLpNorm (fun x => potential alpha c u x * ‖u x‖ ^ (2 + alpha)) 2 volume :=
    eLpNorm_congr_norm_ae hf hm.aestronglyMeasurable (Filter.Eventually.of_forall he)
  refine ⟨hm.congr_norm hf (Filter.Eventually.of_forall fun x => (he x).symm), ?_⟩
  rw [hn]
  simpa [spatialNorm, eLpNorm_norm _ hu6.aestronglyMeasurable] using hb.bound

#print axioms forcing_l2_allocation
#print axioms forcing_scalar_l2_bound
#print axioms forcing_l2_spatial_bound
end HartreeF.ForcingL2
