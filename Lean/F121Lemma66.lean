import F121GeneralAnnularHartree

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.Paper121Lemma66
open EnergySpace EnergySpace.Highpass MassRecovery SobolevStretch WeakHartreeProduct
  StationarySelfTest ForcingDomain BoundedHartreeGradient YoungSource PhysicalLowpass TimeHolder

/-- The coordinate class is controlled by the complete complex Euclidean gradient. -/
theorem coordinate_L1_le_full {U W : V → V}
    (hU : MemLp U 1 volume) (hW : MemLp W 1 volume) (j : Fin 3) :
    ‖AnnularL1.weakGradientOne hU hW j‖ ≤
      (eLpNorm (complexGradient U W) 1 volume).toReal := by
  have he : directionalField U W (coordinate j) = fun x => complexGradient U W x j := by
    funext x
    apply Complex.ext <;>
      simp [directionalField, complexGradient, coordinate, EuclideanSpace.inner_single_right]
  have hd := directionalField_memLp hU hW (coordinate j)
  have hg := memLp_one_iff_integrable.mpr (complexGradient_integrable hU hW)
  have hm : eLpNorm (directionalField U W (coordinate j)) 1 volume ≤
      eLpNorm (complexGradient U W) 1 volume := by
    apply eLpNorm_mono_ae hd.aestronglyMeasurable
    filter_upwards [] with x
    rw [he]
    exact PiLp.norm_apply_le (complexGradient U W x) j
  have hr := ENNReal.toReal_mono hg.eLpNorm_ne_top hm
  simpa only [AnnularL1.weakGradientOne, Lp.norm_toLp] using hr

theorem coordinate_L1_sum_le_three_full {U W : V → V}
    (hU : MemLp U 1 volume) (hW : MemLp W 1 volume) :
    (∑ j : Fin 3, ‖AnnularL1.weakGradientOne hU hW j‖) ≤
      3 * (eLpNorm (complexGradient U W) 1 volume).toReal := by
  calc
    _ ≤ ∑ _j : Fin 3, (eLpNorm (complexGradient U W) 1 volume).toReal :=
      Finset.sum_le_sum (fun j _ => coordinate_L1_le_full hU hW j)
    _ = _ := by simp

/-- One constructed function is simultaneously L1 and L6/5 and has the exact
annular distribution, with no L1 domain hypothesis on the source f. -/
theorem general_annular_full_gradient {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : V → ℂ} {U W : V → V} (hf : MemLp f p volume)
    (hU : MemLp U 1 volume) (hW : MemLp W 1 volume)
    (hwR : HasWeakGradient (fun x => (f x).re) U)
    (hwI : HasWeakGradient (fun x => (f x).im) W)
    (q : GeneralAnnular.Symbol) {L : ℝ} (hL : 0 < L) :
    ∃ g : OneSpace, Integrable (g : V → ℂ) volume ∧
      MemLp (g : V → ℂ) sourceExponent volume ∧
      Lp.toTemperedDistribution g =
        GeneralAnnular.annular q L (Lp.toTemperedDistribution (hf.toLp f)) ∧
      ‖g‖ ≤ (3 * GeneralAnnular.annularConstant q / L) *
        (eLpNorm (complexGradient U W) 1 volume).toReal := by
  let g := GeneralAnnular.annularL1Value q hL (AnnularL1.weakGradientOne hU hW)
  have h := GeneralAnnular.actual_weak_gradient_annular hf hU hW hwR hwI q hL
  refine ⟨g, memLp_one_iff_integrable.mp (Lp.memLp _), ?_, h.1, ?_⟩
  · exact AnnularL1.inverseGradientL1_memLp (by simp [sourceExponent])
      (GeneralAnnular.inverseKernel q hL) (AnnularL1.weakGradientOne hU hW)
  · calc
      ‖g‖ ≤ (GeneralAnnular.annularConstant q / L) *
          ∑ j : Fin 3, ‖AnnularL1.weakGradientOne hU hW j‖ := h.2
      _ ≤ (GeneralAnnular.annularConstant q / L) *
          (3 * (eLpNorm (complexGradient U W) 1 volume).toReal) :=
        mul_le_mul_of_nonneg_left (coordinate_L1_sum_le_three_full hU hW)
          (div_nonneg (GeneralAnnular.annularConstant_nonneg q) hL.le)
      _ = _ := by ring

/-- The exact intermediate expression in the manuscript is bounded by the
original-state Bernstein power, including the zero-gradient case. -/
theorem pureLow_bernstein_chain
    (hD : OrdinaryH1Density) {K α C : ℝ} (hSob : OrdinarySobolev K)
    (hα : 0 < α) (hC : 0 ≤ C) (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    let v := lowEnergyState hD hSob q hM u
    C * (eLpNorm (fun x => energyValue v x) ∞ volume).toReal *
        pureGradientNorm v ^ (4 + 2 * α) ≤
      (C * cutoffYoungConstant q * K ^ ((6 : ℝ)⁻¹)) * Real.sqrt M *
        pureGradientNorm u ^ (5 + 2 * α) := by
  let v := lowEnergyState hD hSob q hM u
  let N := pureGradientNorm u
  have hN : 0 ≤ N := pureGradientNorm_nonneg u
  have hv : 0 ≤ pureGradientNorm v := pureGradientNorm_nonneg v
  have he : 0 ≤ (4 : ℝ) + 2 * α := by linarith
  have hb := lowEnergyState_exact_linf_pureGradient hD hSob q hM u
  have hp : pureGradientNorm v ^ (4 + 2 * α) ≤ N ^ (4 + 2 * α) :=
    Real.rpow_le_rpow hv (lowEnergyState_pureGradient_bound hD hSob q hM u) he
  have hpow : N ^ (5 + 2 * α) = N ^ (4 + 2 * α) * N := by
    rw [show (5 : ℝ) + 2 * α = (4 + 2 * α) + 1 by ring]
    exact Real.rpow_add_one' hN (by linarith)
  have hS : 0 ≤ K ^ ((6 : ℝ)⁻¹) := Real.rpow_nonneg hSob.nonneg _
  change C * (eLpNorm (fun x => energyValue v x) ∞ volume).toReal *
    pureGradientNorm v ^ (4 + 2 * α) ≤ _
  calc
    _ ≤ C * ((cutoffYoungConstant q * Real.sqrt M * K ^ ((6 : ℝ)⁻¹)) * N) *
        pureGradientNorm v ^ (4 + 2 * α) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC) (Real.rpow_nonneg hv _)
    _ ≤ C * ((cutoffYoungConstant q * Real.sqrt M * K ^ ((6 : ℝ)⁻¹)) * N) *
        N ^ (4 + 2 * α) :=
      mul_le_mul_of_nonneg_left hp
        (mul_nonneg hC (mul_nonneg
          (mul_nonneg (mul_nonneg (cutoffYoungConstant_nonneg q) (Real.sqrt_nonneg M)) hS) hN))
    _ = _ := by rw [hpow]; ring

/-- Full Lemma 6.6 terminal: actual weak gradients, both consecutive sharp
bounds, and any fixed smooth annular multiplier with one L1/L6/5 representative.
All ordinary analytic interfaces are explicit; no forcing-L1 input occurs. -/
theorem lemma66_pure_low_leakage
    (hD : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (M : ℝ) (hM : 0 < M) (u : EnergyState),
      let v := lowEnergyState hD hSob q hM u
      let U := energyProjectedGradient Complex.reCLM v
      let W := energyProjectedGradient Complex.imCLM v
      let G := actualFullGradient α c (energyValue v) U W
      HasWeakGradient (fun x => (forcing α c (energyValue v) x).re)
        (forcingGradientRe α c (energyValue v) U W) ∧
      HasWeakGradient (fun x => (forcing α c (energyValue v) x).im)
        (forcingGradientIm α c (energyValue v) U W) ∧
      Integrable G volume ∧
      (eLpNorm G 1 volume).toReal ≤
        C * (eLpNorm (fun x => energyValue v x) ∞ volume).toReal *
          pureGradientNorm v ^ (4 + 2 * α) ∧
      C * (eLpNorm (fun x => energyValue v x) ∞ volume).toReal *
          pureGradientNorm v ^ (4 + 2 * α) ≤
        (C * cutoffYoungConstant q * K ^ ((6 : ℝ)⁻¹)) * Real.sqrt M *
          pureGradientNorm u ^ (5 + 2 * α) ∧
      ∀ (qAnn : GeneralAnnular.Symbol) (L : ℝ), 0 < L →
        ∃ (hf : MemLp (forcing α c (energyValue v)) sourceExponent volume)
          (g : OneSpace),
          Integrable (g : V → ℂ) volume ∧ MemLp (g : V → ℂ) sourceExponent volume ∧
          Lp.toTemperedDistribution g = GeneralAnnular.annular qAnn L
            (Lp.toTemperedDistribution (hf.toLp (forcing α c (energyValue v)))) ∧
          ‖g‖ ≤ (3 * GeneralAnnular.annularConstant qAnn / L) *
            (eLpNorm G 1 volume).toReal := by
  obtain ⟨C, hC0, hC⟩ := lowEnergyState_actualFullGradient_exact_linf hD hSob hH hUpper
  refine ⟨C, hC0, ?_⟩
  intro q M hM u
  let v := lowEnergyState hD hSob q hM u
  have hG := lowEnergyState_forcing_L1_weakGradients_allOrders hD hSob hH hUpper q hM u
  have hSharp := hC q M hM u
  refine ⟨hG.1, hG.2.1, hSharp.1, hSharp.2,
    pureLow_bernstein_chain hD hSob hH.order_pos hC0 q hM u, ?_⟩
  intro qAnn L hL
  obtain ⟨D, hDforce⟩ := forcing_energy_domain_bound hH
  have hf : MemLp (forcing α c (energyValue v)) sourceExponent volume :=
    (hDforce (energyValue v) (Lp.memLp _)).1
  obtain ⟨g, hg1, hg65, hgd, hgn⟩ := general_annular_full_gradient hf
    hG.2.2.1 hG.2.2.2 hG.1 hG.2.1 qAnn hL
  refine ⟨hf, g, hg1, hg65, hgd, ?_⟩
  simpa only [actualFullGradient_eq_complex] using hgn

end HartreeF.Paper121Lemma66
