import F121PureLowGradientSharp

/-! Lemma 6.6 component: actual lowpass Hartree weak derivatives with the
lowpass state's OWN gradient norm. Ordinary analytic interfaces stay explicit. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.BoundedHartreeGradient
open EnergySpace EnergySpace.Highpass PhysicalLowpass SobolevStretch StationarySelfTest
  ForcingDomain WeakHartreeProduct WeakHartreeChain GradientMajorants YoungSource

/-- The finite essential supremum bounds the same actual lowpass representative. -/
theorem lowEnergyState_ae_le_exact_linf
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    ∀ᵐ x ∂volume, ‖energyValue (lowEnergyState hDensity hSob q hM u) x‖ ≤
      (eLpNorm (energyValue (lowEnergyState hDensity hSob q hM u) : V → ℂ) ∞ volume).toReal := by
  have hm := lowEnergyState_memLp_top hDensity hSob q hM u
  have he := enorm_ae_le_eLpNormEssSup
    (energyValue (lowEnergyState hDensity hSob q hM u) : V → ℂ) volume
  rw [← eLpNorm_exponent_top hm.aestronglyMeasurable] at he
  filter_upwards [he] with x hx
  simpa only [toReal_enorm] using ENNReal.toReal_mono hm.eLpNorm_ne_top hx

/-- Bernstein with the original state's pure gradient and no L2 term. -/
theorem lowEnergyState_exact_linf_pureGradient
    (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)
    (q : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState) :
    (eLpNorm (energyValue (lowEnergyState hDensity hSob q hM u) : V → ℂ) ∞ volume).toReal ≤
      (cutoffYoungConstant q * Real.sqrt M * K ^ ((6 : ℝ)⁻¹)) * pureGradientNorm u := by
  calc
    _ ≤ cutoffYoungConstant q * Real.sqrt M * ‖energyValue u‖ :=
      lowEnergyState_linf_bound hDensity hSob q hM u
    _ ≤ cutoffYoungConstant q * Real.sqrt M * (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u) :=
      mul_le_mul_of_nonneg_left (energyValue_le_pureGradient hSob u)
        (mul_nonneg (cutoffYoungConstant_nonneg q) (Real.sqrt_nonneg M))
    _ = _ := by ring

theorem lowEnergyState_forcing_L1_exact_linf_allOrders
    (hDensity : OrdinaryH1Density) {K α c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS α c)
    (hUpper : 1 < α → ∃ c' : ℝ, OrdinaryHLS (α - 1) c') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Cutoff) (M : ℝ) (hM : 0 < M) (u : EnergyState),
      let v := lowEnergyState hDensity hSob q hM u
      let U := energyProjectedGradient Complex.reCLM v
      let V := energyProjectedGradient Complex.imCLM v
      HasWeakGradient (fun x => (forcing α c (energyValue v) x).re)
        (forcingGradientRe α c (energyValue v) U V) ∧
      HasWeakGradient (fun x => (forcing α c (energyValue v) x).im)
        (forcingGradientIm α c (energyValue v) U V) ∧
      MemLp (forcingGradientRe α c (energyValue v) U V) 1 volume ∧
      MemLp (forcingGradientIm α c (energyValue v) U V) 1 volume ∧
      (eLpNorm (forcingGradientRe α c (energyValue v) U V) 1 volume).toReal +
        (eLpNorm (forcingGradientIm α c (energyValue v) U V) 1 volume).toReal ≤
        C * (eLpNorm (energyValue v : V → ℂ) ∞ volume).toReal * pureGradientNorm v ^ (4 + 2 * α) := by
  obtain ⟨C, hC0, hC⟩ :=
    lowEnergyState_forcing_L1_sameState_allOrders hDensity hSob hH hUpper
  refine ⟨C, hC0, ?_⟩
  intro q M hM u
  exact hC q M hM u _ ENNReal.toReal_nonneg
    (lowEnergyState_ae_le_exact_linf hDensity hSob q hM u)

end HartreeF.BoundedHartreeGradient
