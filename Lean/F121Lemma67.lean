import FActualUpperProjectedGradientL1
import F121Lemma66

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace
namespace HartreeF.Paper121Lemma67
open EnergySpace EnergySpace.Highpass PhysicalLowpass SobolevStretch StationarySelfTest
  ForcingDomain WeakHartreeProduct WeakHartreeChain BoundedHartreeGradient
  GradientMajorants ActualUpperProduct YoungSource MassRecovery

/-- The literal product in Lemma 6.7, with the signed real density unchanged. -/
def weightedMixedProduct (α c : ℝ) (d : Space → ℝ) (v : EnergyState) : Space → ℂ :=
  fun x => rieszConvolution α c d x • localFactor α (energyValue v) x

/-- The explicit finite constant left by the two real projections of the
weighted mixed gradient. -/
def weightedMixedConstant (K α c : ℝ) : ℝ :=
  2 * c * ((3 - α) * (4 ^ ((4 - α) / 2) * K ^ ((α - 2) / 2)) +
    6 * (α + 2) * (2 ^ (3 - α) * K ^ ((α - 2) / 2)))

theorem weightedMixedConstant_nonneg {K α c : ℝ} (hK : 0 ≤ K)
    (hα2 : 2 < α) (hα3 : α < 3) (hc : 0 < c) :
    0 ≤ weightedMixedConstant K α c := by
  unfold weightedMixedConstant
  have h32 : 0 ≤ 3 - α := by linarith
  have hαp : 0 ≤ α + 2 := by linarith
  positivity

/-- The historical weighted-product budget has exactly the manuscript powers. -/
theorem two_upperProjectedGradientL1Bound_eq (K α c M N mass : ℝ) :
    2 * upperProjectedGradientL1Bound K α c M N mass =
      weightedMixedConstant K α c * M ^ (4 - α) * N ^ (2 * α - 2) * mass := by
  rw [upperProjectedGradientL1Bound_eq]
  unfold weightedMixedConstant
  ring

/-- Strict HLS at order alpha supplies the independent L6/5 domain of the
same literal product. No derivative-order HLS premise occurs. -/
theorem weightedMixedProduct_memLp {α c : ℝ} (hH : OrdinaryHLS α c)
    {d : Space → ℝ} (hd : MemLp d (ENNReal.ofReal (densityExponent α)) volume)
    (v : EnergyState) :
    MemLp (weightedMixedProduct α c d v) sourceExponent volume := by
  obtain ⟨hq1, hqα, hr, hrel⟩ := energyHLS_range hH.order_pos hH.order_lt_three
  obtain ⟨_C, hC⟩ := hH.strong_bound _ _ hq1 hqα hr hrel
  obtain ⟨_hdom, hp, _hbound⟩ := hC d hd
  have hb : MemLp (localFactor α (energyValue v))
      (ENNReal.ofReal (energyOuterExponent α)) volume :=
    localFactor_memLp hH.order_pos (by simpa using Lp.memLp (energyValue v))
  let := (energy_holder hH.order_pos hH.order_lt_three).ennrealOfReal
  change MemLp (fun x => rieszConvolution α c d x • localFactor α (energyValue v) x)
    (ENNReal.ofReal (6 / 5 : ℝ)) volume
  exact hp.smul hb

/-- Projection of the literal complex product has the literal product-rule
field as weak gradient. The density is only assumed integrable here. -/
theorem weightedMixedProduct_projected_hasWeakGradient
    (hD : OrdinaryH1Density) {K α c M : ℝ} (hS : OrdinarySobolev K)
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hM : 0 ≤ M)
    (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1) (v : EnergyState)
    {d : Space → ℝ} (hd : Integrable d volume)
    (hv10 : MemLp (energyValue v) 10 volume)
    (hU : MemLp (energyProjectedGradient Complex.reCLM v)
      (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hV : MemLp (energyProjectedGradient Complex.imCLM v)
      (ENNReal.ofReal (30 / 13 : ℝ)) volume)
    (hvM : ∀ᵐ x ∂volume, ‖energyValue v x‖ ≤ M) :
    HasWeakGradient (fun x => A (weightedMixedProduct α c d v x))
      (actualRieszLocalFactorGradient α c A d (energyValue v)
        (energyProjectedGradient Complex.reCLM v)
        (energyProjectedGradient Complex.imCLM v)) := by
  have hw := actual_riesz_projectedLocalFactor_hasWeakGradient
    hD hS hα2 hα3 hc hM A hA hd (energyState_inDotH1 v) hv10 hU hV hvM
  convert hw using 1
  funext x
  change A (rieszConvolution α c d x • localFactor α (energyValue v) x) =
    rieszConvolution α c d x * A (WeakHartreeChain.localFactor (1 + α) (energyValue v x))
  rw [map_smul, smul_eq_mul]
  rfl

/-- For an integrable function, the manuscript L1 norm is the integral of its
pointwise norm. -/
theorem eLpNorm_one_toReal_eq_integral_norm {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} (hf : Integrable f volume) :
    (eLpNorm f 1 volume).toReal = ∫ x, ‖f x‖ := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  exact (integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable).symm

/-- Full Lemma 6.7: the same actual product is in L6/5, its two actual weak
coordinate gradients combine to an L1 complex Euclidean gradient with the
weighted Hardy scaling, and Lemma 6.6's annular inverse-gradient conclusion
applies to this product. -/
theorem lemma67_weighted_mixed_gradient_replacement
    (hD : OrdinaryH1Density) {K α c : ℝ} (hS : OrdinarySobolev K)
    (hH : OrdinaryHLS α c) (hα2 : 2 < α)
    (qLow : Cutoff) {M : ℝ} (hM : 0 < M) (u : EnergyState)
    {d : Space → ℝ} (hd1 : Integrable d volume)
    (hd0 : MemLp d (ENNReal.ofReal (densityExponent α)) volume) :
    let v := lowEnergyState hD hS qLow hM u
    let T := weightedMixedProduct α c d v
    let GR := actualRieszLocalFactorGradient α c Complex.reCLM d (energyValue v)
      (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)
    let GI := actualRieszLocalFactorGradient α c Complex.imCLM d (energyValue v)
      (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)
    let G := complexGradient GR GI
    let A := (eLpNorm (energyValue v : Space → ℂ) ∞ volume).toReal
    0 ≤ weightedMixedConstant K α c ∧
    MemLp T sourceExponent volume ∧
    HasWeakGradient (fun x => (T x).re) GR ∧
    HasWeakGradient (fun x => (T x).im) GI ∧
    Integrable G volume ∧
    (eLpNorm G 1 volume).toReal ≤ weightedMixedConstant K α c *
      (eLpNorm d 1 volume).toReal * A ^ (4 - α) *
        pureGradientNorm v ^ (2 * α - 2) ∧
    ∀ (qAnn : GeneralAnnular.Symbol) (L : ℝ), 0 < L →
      ∃ g : OneSpace, Integrable (g : Space → ℂ) volume ∧
        MemLp (g : Space → ℂ) sourceExponent volume ∧
        Lp.toTemperedDistribution g = GeneralAnnular.annular qAnn L
          (Lp.toTemperedDistribution ((weightedMixedProduct_memLp hH hd0 v).toLp T)) ∧
        ‖g‖ ≤ (3 * GeneralAnnular.annularConstant qAnn / L) *
          (eLpNorm G 1 volume).toReal := by
  let v := lowEnergyState hD hS qLow hM u
  let T := weightedMixedProduct α c d v
  let GR := actualRieszLocalFactorGradient α c Complex.reCLM d (energyValue v)
    (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)
  let GI := actualRieszLocalFactorGradient α c Complex.imCLM d (energyValue v)
    (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)
  let G := complexGradient GR GI
  let A := (eLpNorm (energyValue v : Space → ℂ) ∞ volume).toReal
  have hα2' : 2 ≤ α := hα2.le
  have hvA : ∀ᵐ x ∂volume, ‖energyValue v x‖ ≤ A :=
    lowEnergyState_ae_le_exact_linf hD hS qLow hM u
  have hR := actualRieszLocalFactorGradient_energy_L1 hD hS hα2'
    hH.order_lt_three hH.normalization_pos ENNReal.toReal_nonneg
    Complex.reCLM reCLM_norm_le_one v hvA hd1
  have hI := actualRieszLocalFactorGradient_energy_L1 hD hS hα2'
    hH.order_lt_three hH.normalization_pos ENNReal.toReal_nonneg
    Complex.imCLM imCLM_norm_le_one v hvA hd1
  have hwR : HasWeakGradient (fun x => (T x).re) GR := by
    simpa [T, GR] using
      (weightedMixedProduct_projected_hasWeakGradient hD hS hα2'
        hH.order_lt_three hH.normalization_pos ENNReal.toReal_nonneg
        Complex.reCLM reCLM_norm_le_one v hd1
        (lowEnergyState_memLp_ten hD hS qLow hM u)
        (lowEnergyState_projectedGradient_memLp_thirty_thirteen
          hD hS Complex.reCLM qLow hM u)
        (lowEnergyState_projectedGradient_memLp_thirty_thirteen
          hD hS Complex.imCLM qLow hM u) hvA)
  have hwI : HasWeakGradient (fun x => (T x).im) GI := by
    simpa [T, GI] using
      (weightedMixedProduct_projected_hasWeakGradient hD hS hα2'
        hH.order_lt_three hH.normalization_pos ENNReal.toReal_nonneg
        Complex.imCLM imCLM_norm_le_one v hd1
        (lowEnergyState_memLp_ten hD hS qLow hM u)
        (lowEnergyState_projectedGradient_memLp_thirty_thirteen
          hD hS Complex.reCLM qLow hM u)
        (lowEnergyState_projectedGradient_memLp_thirty_thirteen
          hD hS Complex.imCLM qLow hM u) hvA)
  have hT : MemLp T sourceExponent volume := by
    simpa only [T] using weightedMixedProduct_memLp hH hd0 v
  have hGR : MemLp GR 1 volume := by simpa only [GR] using hR.1
  have hGI : MemLp GI 1 volume := by simpa only [GI] using hI.1
  have hGint : Integrable G volume := by
    simpa only [G] using complexGradient_integrable hGR hGI
  have hGbound : (eLpNorm G 1 volume).toReal ≤
      2 * upperProjectedGradientL1Bound K α c A (pureGradientNorm v) (∫ y, ‖d y‖) := by
    have hs := complexGradient_L1_norm_le hGR hGI
    have hRb := hR.2
    have hIb := hI.2
    change (eLpNorm GR 1 volume).toReal ≤
      upperProjectedGradientL1Bound K α c A (pureGradientNorm v) (∫ y, ‖d y‖) at hRb
    change (eLpNorm GI 1 volume).toReal ≤
      upperProjectedGradientL1Bound K α c A (pureGradientNorm v) (∫ y, ‖d y‖) at hIb
    linarith
  have hmass := eLpNorm_one_toReal_eq_integral_norm hd1
  have hGsharp : (eLpNorm G 1 volume).toReal ≤ weightedMixedConstant K α c *
      (eLpNorm d 1 volume).toReal * A ^ (4 - α) *
        pureGradientNorm v ^ (2 * α - 2) := by
    calc
      _ ≤ 2 * upperProjectedGradientL1Bound K α c A (pureGradientNorm v)
          (∫ y, ‖d y‖) := hGbound
      _ = 2 * upperProjectedGradientL1Bound K α c A (pureGradientNorm v)
          (eLpNorm d 1 volume).toReal := by rw [hmass]
      _ = _ := by
        rw [two_upperProjectedGradientL1Bound_eq]
        ring
  refine ⟨weightedMixedConstant_nonneg hS.nonneg hα2 hH.order_lt_three
    hH.normalization_pos, hT, hwR, hwI, hGint, hGsharp, ?_⟩
  intro qAnn L hL
  exact Paper121Lemma66.general_annular_full_gradient hT hGR hGI hwR hwI qAnn hL

end HartreeF.Paper121Lemma67
