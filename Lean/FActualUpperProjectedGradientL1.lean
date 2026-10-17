import FActualRieszWeightedDomination
import FActualRieszL1ProductWeakGradient
import FEnergyStateWeakGradient

/-!
STATIC DRAFT ONLY: not elaborated, compiled, or kernel checked.
The actual vector expression is proved globally L1 by scalar weighted products.
This module alone does not assert a weak derivative identity or global L1 of
an unprojected G2 function. No OrdinaryHLS premise is used.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal

namespace HartreeF.ActualUpperProduct
open EnergySpace SobolevStretch StationarySelfTest WeakHartreeChain ForcingDomain
  RieszConvolutionDerivative RieszKernelDerivative RieszWeakDerivative WeightedRieszProduct
  GradientMajorants BoundedHartreeGradient MixedRemainderLp

/-- The literal finite-sum projected gradient, with no choice of representative. -/
theorem energyProjectedGradient_norm_le_coordinate_sum
    (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1) (v : EnergyState) (x : Space) :
    ‖energyProjectedGradient A v x‖ ≤ ∑ j : Fin 3, ‖energyGradient j v x‖ := by
  classical
  unfold energyProjectedGradient
  calc
    _ ≤ ∑ j : Fin 3, ‖A (energyGradient j v x) • coordinate j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, ‖energyGradient j v x‖ := by
      apply Finset.sum_le_sum
      intro j _
      have hp : ‖A (energyGradient j v x)‖ ≤ ‖energyGradient j v x‖ := by
        calc
          _ ≤ ‖A‖ * ‖energyGradient j v x‖ := A.le_opNorm _
          _ ≤ 1 * ‖energyGradient j v x‖ :=
            mul_le_mul_of_nonneg_right hA (norm_nonneg _)
          _ = _ := one_mul _
      have hc : ‖coordinate j‖ = 1 := by simp [coordinate]
      simpa only [norm_smul, hc, mul_one] using hp

/-- The factor two is solely the sum of the two canonical real projections. -/
theorem energyProjectedGradient_real_imag_norm_sum_le (v : EnergyState) (x : Space) :
    ‖energyProjectedGradient Complex.reCLM v x‖ +
      ‖energyProjectedGradient Complex.imCLM v x‖ ≤
        2 * ∑ j : Fin 3, ‖energyGradient j v x‖ := by
  have hr := energyProjectedGradient_norm_le_coordinate_sum
    Complex.reCLM reCLM_norm_le_one v x
  have hi := energyProjectedGradient_norm_le_coordinate_sum
    Complex.imCLM imCLM_norm_le_one v x
  linarith

/-- The explicit local-factor formula agrees with the actual C1 chain derivative. -/
theorem projectedLocalFactorGradient_eq_chain {q : ℝ} (hq : 1 < q)
    (A : ℂ →L[ℝ] ℝ) (u : Space → ℂ) (U V : Space → Space) :
    projectedLocalFactorGradient q A u U V =
      complexChainGradient (projectedLocalFactor q A) u U V := by
  funext x
  simp only [projectedLocalFactorGradient, complexChainGradient,
    projectedLocalFactor_fderiv hq, ContinuousLinearMap.comp_apply]

/-- Exact q+1 coefficient from the proved local-factor differential. -/
theorem projectedLocalFactorGradient_norm_le {q : ℝ} (hq : 1 < q)
    (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1)
    (u : Space → ℂ) (U V : Space → Space) (x : Space) :
    ‖projectedLocalFactorGradient q A u U V x‖ ≤
      (q + 1) * ‖u x‖ ^ q * (‖U x‖ + ‖V x‖) := by
  rw [projectedLocalFactorGradient_eq_chain hq]
  simpa only [powerGradientMajorant, mul_assoc] using
    complexChainGradient_bound (projectedLocalFactor_fderiv_bound hq A hA) u U V x

/-- Literal convolution/chain expression is measurable before any weak identity. -/
theorem actualRieszLocalFactorGradient_aestronglyMeasurable
    {α c : ℝ} (hα : 0 < α) (A : ℂ →L[ℝ] ℝ)
    {h : Space → ℝ} (hh : Integrable h volume)
    {u : Space → ℂ} {U V : Space → Space}
    (hu : AEStronglyMeasurable u volume)
    (hU : AEStronglyMeasurable U volume) (hV : AEStronglyMeasurable V volume) :
    AEStronglyMeasurable (actualRieszLocalFactorGradient α c A h u U V) volume := by
  have hq : 1 < 1 + α := by linarith
  have hg : AEStronglyMeasurable (gradientConvolution α c h) volume :=
    hh.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      (rieszKernelGradient_measurable α c).aestronglyMeasurable
  have hp0 : AEStronglyMeasurable
      (fun x => ∫ y, h y * rieszKernel α c (x-y)) volume :=
    hh.aestronglyMeasurable.convolution (ContinuousLinearMap.mul ℝ ℝ)
      (rieszKernel_measurable α c).aestronglyMeasurable
  have hp_eq : (fun x => ∫ y, h y * rieszKernel α c (x-y)) =
      rieszConvolution α c h := by
    funext x
    unfold rieszConvolution
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [hp_eq] at hp0
  have hb := (projectedLocalFactor_contDiff_one hq A).continuous.comp_aestronglyMeasurable hu
  have hB : AEStronglyMeasurable (projectedLocalFactorGradient (1+α) A u U V) volume := by
    rw [projectedLocalFactorGradient_eq_chain hq]
    exact complexChainGradient_aestronglyMeasurable
      (projectedLocalFactor_contDiff_one hq A) hu hU hV
  exact (hb.smul hg).add (hp0.smul hB)

/-- Pointwise domination by the SAME actual scalar weighted products. -/
theorem actualRieszLocalFactorGradient_energy_norm_le
    {α c : ℝ} (hα2 : 2 ≤ α) (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1)
    (h : Space → ℝ) (v : EnergyState) (x : Space) :
    ‖actualRieszLocalFactorGradient α c A h (energyValue v)
      (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v) x‖ ≤
      ‖gradientConvolution α c h x‖ * ‖energyValue v x‖ ^ (α+2) +
        (2 * (α+2)) * ∑ j : Fin 3,
          ‖rieszConvolution α c h x‖ * ‖energyValue v x‖ ^ (α+1) *
            ‖energyGradient j v x‖ := by
  have hq : 1 < 1 + α := by linarith
  have hb : ‖projectedLocalFactor (1+α) A (energyValue v x)‖ ≤
      ‖energyValue v x‖ ^ (α+2) := by
    simpa only [one_mul, show 1+α+1 = α+2 by ring] using
      projectedLocalFactor_norm_bound hq A hA (energyValue v x)
  have hB0 := projectedLocalFactorGradient_norm_le hq A hA (energyValue v)
    (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v) x
  have hB : ‖projectedLocalFactorGradient (1+α) A (energyValue v)
      (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v) x‖ ≤
      (α+2) * ‖energyValue v x‖ ^ (α+1) *
        (2 * ∑ j : Fin 3, ‖energyGradient j v x‖) := by
    calc
      _ ≤ (α+2) * ‖energyValue v x‖ ^ (α+1) *
          (‖energyProjectedGradient Complex.reCLM v x‖ +
            ‖energyProjectedGradient Complex.imCLM v x‖) := by
        simpa only [show 1+α = α+1 by ring, show α+1+1 = α+2 by ring] using hB0
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (energyProjectedGradient_real_imag_norm_sum_le v x)
        (mul_nonneg (by linarith : 0 ≤ α+2) (Real.rpow_nonneg (norm_nonneg _) _))
  unfold actualRieszLocalFactorGradient
  calc
    _ ≤ ‖projectedLocalFactor (1+α) A (energyValue v x) • gradientConvolution α c h x‖ +
        ‖rieszConvolution α c h x • projectedLocalFactorGradient (1+α) A (energyValue v)
          (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v) x‖ :=
      norm_add_le _ _
    _ ≤ ‖energyValue v x‖^(α+2) * ‖gradientConvolution α c h x‖ +
        ‖rieszConvolution α c h x‖ *
          ((α+2) * ‖energyValue v x‖^(α+1) *
            (2 * ∑ j : Fin 3, ‖energyGradient j v x‖)) := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hB (norm_nonneg _))
    _ = _ := by
      rw [← Finset.mul_sum]
      ring

/-- Exact finite constant. N is the original state's pureGradientNorm. -/
def upperProjectedGradientL1Bound (K α c M N mass : ℝ) : ℝ :=
  c * ((3-α) * derivativeConstant K α N +
    6 * (α+2) * localGradientConstant K α N) * M^(4-α) * mass

/-- Expanded constant displays the common N^(2α-2) factor. -/
theorem upperProjectedGradientL1Bound_eq (K α c M N mass : ℝ) :
    upperProjectedGradientL1Bound K α c M N mass =
      c * ((3-α) * (4 ^ ((4-α)/2) * K ^ ((α-2)/2)) +
        6 * (α+2) * (2 ^ (3-α) * K ^ ((α-2)/2))) *
          M^(4-α) * N^(2*α-2) * mass := by
  unfold upperProjectedGradientL1Bound derivativeConstant localGradientConstant
  ring

/-- Actual MemLp1 and finite actualNorm bound of the literal vector expression.
The ordinary density/Sobolev hypotheses are consumed only by the scalar weighted
product producers. No assumed vector-gradient estimate or weak identity occurs. -/
theorem actualRieszLocalFactorGradient_energy_L1
    (hDensity : OrdinaryH1Density) {K α c M : ℝ} (hSob : OrdinarySobolev K)
    (hα2 : 2 ≤ α) (hα3 : α < 3) (hc : 0 < c) (hM : 0 ≤ M)
    (A : ℂ →L[ℝ] ℝ) (hA : ‖A‖ ≤ 1) (v : EnergyState)
    (hvM : ∀ᵐ x ∂volume, ‖energyValue v x‖ ≤ M)
    {h : Space → ℝ} (hh : Integrable h volume) :
    MemLp (actualRieszLocalFactorGradient α c A h (energyValue v)
      (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)) 1 volume ∧
    actualNorm 1 (actualRieszLocalFactorGradient α c A h (energyValue v)
      (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)) ≤
      upperProjectedGradientL1Bound K α c M (pureGradientNorm v) (∫ y, ‖h y‖) := by
  let D : Space → ℝ := fun x => ‖gradientConvolution α c h x‖ * ‖energyValue v x‖^(α+2)
  let W : Fin 3 → Space → ℝ := fun j x =>
    ‖rieszConvolution α c h x‖ * ‖energyValue v x‖^(α+1) * ‖energyGradient j v x‖
  let DB : ℝ := (c*(3-α)) * ((M^(4-α) * derivativeConstant K α (pureGradientNorm v)) * ∫ y, ‖h y‖)
  let WB : ℝ := c * ((M^(4-α) * localGradientConstant K α (pureGradientNorm v)) * ∫ y, ‖h y‖)
  have hD0 := actual_potentialGradient_weighted_L1 hDensity hSob hα2 hα3 hc hM v hvM hh
  have hW0 := fun j => actual_potential_weighted_coordinate_L1
    hDensity hSob hα2 hα3 hc hM v hvM hh j
  have hD : SpatialBound D 1 DB := by
    refine ⟨by norm_num, ?_, ?_⟩
    · simpa only [one_div_one, ENNReal.ofReal_one] using hD0.1
    · simpa only [spatialNorm, actualNorm, one_div_one, ENNReal.ofReal_one] using hD0.2
  have hW (j : Fin 3) : SpatialBound (W j) 1 WB := by
    refine ⟨by norm_num, ?_, ?_⟩
    · simpa only [one_div_one, ENNReal.ofReal_one] using (hW0 j).1
    · simpa only [spatialNorm, actualNorm, one_div_one, ENNReal.ofReal_one] using (hW0 j).2
  have hsum := ((hW 0).add (hW 1) (by norm_num)).add (hW 2) (by norm_num)
  have hmajor := hD.add (spatialBound_const_mul hsum
    (by linarith : 0 ≤ 2 * (α+2))) (by norm_num)
  have hmeas := actualRieszLocalFactorGradient_aestronglyMeasurable (c := c)
    (by linarith : 0 < α) A hh (Lp.aestronglyMeasurable (energyValue v))
    (energyProjectedGradient_memLp Complex.reCLM v).aestronglyMeasurable
    (energyProjectedGradient_memLp Complex.imCLM v).aestronglyMeasurable
  have hd := domain_bound_of_spatialBound hmajor hmeas (Eventually.of_forall fun x => by
    simpa only [D, W, Fin.sum_univ_three] using
      actualRieszLocalFactorGradient_energy_norm_le hα2 A hA h v x)
  have hd' :
      MemLp (actualRieszLocalFactorGradient α c A h (energyValue v)
        (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)) 1 volume ∧
      actualNorm 1 (actualRieszLocalFactorGradient α c A h (energyValue v)
        (energyProjectedGradient Complex.reCLM v) (energyProjectedGradient Complex.imCLM v)) ≤
        DB + (2 * (α+2)) * ((WB + WB) + WB) := by
    simpa only [one_div_one, ENNReal.ofReal_one] using hd
  refine ⟨hd'.1, hd'.2.trans_eq ?_⟩
  dsimp [DB, WB, upperProjectedGradientL1Bound]
  ring

#print axioms energyProjectedGradient_norm_le_coordinate_sum
#print axioms energyProjectedGradient_real_imag_norm_sum_le
#print axioms actualRieszLocalFactorGradient_energy_norm_le
#print axioms actualRieszLocalFactorGradient_energy_L1
end HartreeF.ActualUpperProduct
