import FSameStateWeightedRieszSlices
import FNonnegativeKernelTonelli

/-! STATIC-ONLY CANDIDATE.
Genuine upper-order L1-source weighted product estimates, 2 <= alpha < 3.
No HLS input and no desired estimate, convolution domain, or original-value L2
hypothesis occurs. Weak Leibniz identification of an actual Hartree gradient is
not claimed here and remains a separate theorem. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HartreeF.WeightedRieszProduct
open EnergySpace SobolevStretch StationarySelfTest WeightedHardy GradientMajorants

def derivativeProductMajorant (α : ℝ) (h : V → ℝ) (u : EnergyState) (x : V) : ℝ :=
  ∫ y, ‖h y‖ * derivativeSlice α u y x

def localGradientProductMajorant (α : ℝ) (h : V → ℝ)
    (u : EnergyState) (j : Fin 3) (x : V) : ℝ :=
  ∫ y, ‖h y‖ * localGradientSlice α u j y x

/-- Exact factorization into the literal scalar kernel convolution and actual value. -/
theorem derivativeProductMajorant_eq (α : ℝ) (h : V → ℝ) (u : EnergyState) (x : V) :
    derivativeProductMajorant α h u x =
      (∫ y, ‖x - y‖ ^ (α - 4) * ‖h y‖) * ‖energyValue u x‖ ^ (α + 2) := by
  unfold derivativeProductMajorant derivativeSlice
  calc
    _ = ∫ y, (‖x - y‖ ^ (α - 4) * ‖h y‖) * ‖energyValue u x‖ ^ (α + 2) := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := integral_mul_const _ _

/-- Exact factorization for the local differentiation term. -/
theorem localGradientProductMajorant_eq (α : ℝ) (h : V → ℝ)
    (u : EnergyState) (j : Fin 3) (x : V) :
    localGradientProductMajorant α h u j x =
      (∫ y, ‖x - y‖ ^ (α - 3) * ‖h y‖) *
        ‖energyValue u x‖ ^ (α + 1) * ‖energyGradient j u x‖ := by
  unfold localGradientProductMajorant localGradientSlice
  calc
    _ = ∫ y, (‖x - y‖ ^ (α - 3) * ‖h y‖) *
        (‖energyValue u x‖ ^ (α + 1) * ‖energyGradient j u x‖) := by
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := by rw [integral_mul_const]; ring

theorem derivativeSlice_joint_aestronglyMeasurable (α : ℝ) (u : EnergyState) :
    AEStronglyMeasurable (fun z : V × V => derivativeSlice α u z.2 z.1)
      (volume.prod volume) := by
  have hd : Measurable (fun z : V × V => ‖z.1 - z.2‖ ^ (α - 4)) :=
    (measurable_fst.sub measurable_snd).norm.pow_const _
  exact hd.aestronglyMeasurable.mul (value_power_aestronglyMeasurable u (α + 2)).comp_fst

theorem localGradientSlice_joint_aestronglyMeasurable
    (α : ℝ) (u : EnergyState) (j : Fin 3) :
    AEStronglyMeasurable (fun z : V × V => localGradientSlice α u j z.2 z.1)
      (volume.prod volume) := by
  have hd : Measurable (fun z : V × V => ‖z.1 - z.2‖ ^ (α - 3)) :=
    (measurable_fst.sub measurable_snd).norm.pow_const _
  exact (hd.aestronglyMeasurable.mul
    (value_power_aestronglyMeasurable u (α + 1)).comp_fst).mul
      (Lp.aestronglyMeasurable (energyGradient j u)).norm.comp_fst

/-- The derivative-kernel term, with its full two-point absolute-integrability domain. -/
theorem derivativeProduct_domain_bound (hDensity : OrdinaryH1Density)
    {K α A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A)
    {h : V → ℝ} (hh : Integrable h volume) :
    Integrable (fun z : V × V => ‖h z.2‖ * derivativeSlice α u z.2 z.1)
      (volume.prod volume) ∧
    (∀ᵐ x ∂volume, Integrable (fun y => ‖h y‖ * derivativeSlice α u y x) volume) ∧
    SpatialBound (derivativeProductMajorant α h u) 1
      ((A ^ (4 - α) * derivativeConstant K α (pureGradientNorm u)) * ∫ y, ‖h y‖) := by
  exact nonnegative_kernel_tonelli (derivativeSlice_joint_aestronglyMeasurable α u)
    (fun z => derivativeSlice_nonneg α u z.2 z.1)
    (fun y => (nonnegative_integral_of_spatialBound_one
      (derivativeSlice_spatialBound hDensity hSob hα2 hα3 hA0 u hA y)
      (derivativeSlice_nonneg α u y)).2) hh

/-- The local-gradient term, derived by actual Hardy/Cauchy and Tonelli. -/
theorem localGradientProduct_domain_bound (hDensity : OrdinaryH1Density)
    {K α A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A)
    {h : V → ℝ} (hh : Integrable h volume) (j : Fin 3) :
    Integrable (fun z : V × V => ‖h z.2‖ * localGradientSlice α u j z.2 z.1)
      (volume.prod volume) ∧
    (∀ᵐ x ∂volume, Integrable (fun y => ‖h y‖ * localGradientSlice α u j y x) volume) ∧
    SpatialBound (localGradientProductMajorant α h u j) 1
      ((A ^ (4 - α) * localGradientConstant K α (pureGradientNorm u)) * ∫ y, ‖h y‖) := by
  exact nonnegative_kernel_tonelli (localGradientSlice_joint_aestronglyMeasurable α u j)
    (fun z => localGradientSlice_nonneg α u j z.2 z.1)
    (fun y => (nonnegative_integral_of_spatialBound_one
      (localGradientSlice_spatialBound hDensity hSob hα2 hα3 hA0 u hA j y)
      (localGradientSlice_nonneg α u j y)).2) hh

/-- Both genuine weighted-product L1 norms with the exact common scaling. -/
theorem weightedProducts_integral_domain_bound (hDensity : OrdinaryH1Density)
    {K α A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A)
    {h : V → ℝ} (hh : Integrable h volume) (j : Fin 3) :
    (MemLp (derivativeProductMajorant α h u) 1 volume ∧
      Integrable (derivativeProductMajorant α h u) volume ∧
      (∫ x, derivativeProductMajorant α h u x) ≤
        ((A ^ (4 - α) * derivativeConstant K α (pureGradientNorm u)) * ∫ y, ‖h y‖)) ∧
    (MemLp (localGradientProductMajorant α h u j) 1 volume ∧
      Integrable (localGradientProductMajorant α h u j) volume ∧
      (∫ x, localGradientProductMajorant α h u j x) ≤
        ((A ^ (4 - α) * localGradientConstant K α (pureGradientNorm u)) * ∫ y, ‖h y‖)) := by
  constructor
  · apply nonnegative_integral_of_spatialBound_one
      (derivativeProduct_domain_bound hDensity hSob hα2 hα3 hA0 u hA hh).2.2
    intro x
    exact integral_nonneg fun y => mul_nonneg (norm_nonneg _) (derivativeSlice_nonneg α u y x)
  · apply nonnegative_integral_of_spatialBound_one
      (localGradientProduct_domain_bound hDensity hSob hα2 hα3 hA0 u hA hh j).2.2
    intro x
    exact integral_nonneg fun y => mul_nonneg (norm_nonneg _) (localGradientSlice_nonneg α u j y x)

/-- Endpoint constants are exactly 4 and 2, without using order-zero HLS. -/
theorem order_two_constants (K N : ℝ) :
    derivativeConstant K 2 N = 4 * N ^ (2 : ℕ) ∧
    localGradientConstant K 2 N = 2 * N ^ (2 : ℕ) := by
  constructor <;> norm_num [derivativeConstant, localGradientConstant, Real.rpow_ofNat]

/-- Public literal-integral form; no auxiliary representatives occur in the statement. -/
theorem actual_weighted_kernel_integrals (hDensity : OrdinaryH1Density)
    {K α A : ℝ} (hSob : OrdinarySobolev K) (hα2 : 2 ≤ α) (hα3 : α < 3)
    (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A)
    {h : V → ℝ} (hh : Integrable h volume) (j : Fin 3) :
    (Integrable (fun x => (∫ y, ‖x - y‖ ^ (α - 4) * ‖h y‖) *
        ‖energyValue u x‖ ^ (α + 2)) volume ∧
      (∫ x, (∫ y, ‖x - y‖ ^ (α - 4) * ‖h y‖) * ‖energyValue u x‖ ^ (α + 2)) ≤
        ((A ^ (4 - α) * derivativeConstant K α (pureGradientNorm u)) * ∫ y, ‖h y‖)) ∧
    (Integrable (fun x => (∫ y, ‖x - y‖ ^ (α - 3) * ‖h y‖) *
        ‖energyValue u x‖ ^ (α + 1) * ‖energyGradient j u x‖) volume ∧
      (∫ x, (∫ y, ‖x - y‖ ^ (α - 3) * ‖h y‖) *
        ‖energyValue u x‖ ^ (α + 1) * ‖energyGradient j u x‖) ≤
        ((A ^ (4 - α) * localGradientConstant K α (pureGradientNorm u)) * ∫ y, ‖h y‖)) := by
  have hb := weightedProducts_integral_domain_bound hDensity hSob hα2 hα3 hA0 u hA hh j
  have hd := funext (derivativeProductMajorant_eq α h u)
  have hl := funext (localGradientProductMajorant_eq α h u j)
  rw [hd, hl] at hb
  exact ⟨hb.1.2, hb.2.2⟩

/-- Explicit alpha=2 consumer, whose proof branches above invoke actual Hardy. -/
theorem order_two_weightedProducts (hDensity : OrdinaryH1Density)
    {K A : ℝ} (hSob : OrdinarySobolev K) (hA0 : 0 ≤ A) (u : EnergyState)
    (hA : ∀ᵐ x ∂volume, ‖energyValue u x‖ ≤ A)
    {h : V → ℝ} (hh : Integrable h volume) (j : Fin 3) :
    SpatialBound (derivativeProductMajorant 2 h u) 1
      ((A ^ (2 : ℕ) * (4 * pureGradientNorm u ^ (2 : ℕ))) * ∫ y, ‖h y‖) ∧
    SpatialBound (localGradientProductMajorant 2 h u j) 1
      ((A ^ (2 : ℕ) * (2 * pureGradientNorm u ^ (2 : ℕ))) * ∫ y, ‖h y‖) := by
  constructor
  · simpa only [show (4 - 2 : ℝ) = 2 by norm_num, Real.rpow_ofNat,
      (order_two_constants K (pureGradientNorm u)).1] using
      (derivativeProduct_domain_bound hDensity hSob (by norm_num : (2 : ℝ) ≤ 2)
        (by norm_num : (2 : ℝ) < 3) hA0 u hA hh).2.2
  · simpa only [show (4 - 2 : ℝ) = 2 by norm_num, Real.rpow_ofNat,
      (order_two_constants K (pureGradientNorm u)).2] using
      (localGradientProduct_domain_bound hDensity hSob (by norm_num : (2 : ℝ) ≤ 2)
        (by norm_num : (2 : ℝ) < 3) hA0 u hA hh j).2.2

end HartreeF.WeightedRieszProduct
