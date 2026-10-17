import FActualCompactPDEToChargeDerivative
import FActualUniformChargeFlux
import CutoffL3Scaling
import FLocalMildTrajectoryToDomainPDE
import FActualMaximalMildTrajectory
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Literal terminal wrapper for Lemma 3.8 of the 121-page manuscript.
For an arbitrary real smooth compact cutoff it derives the localized charge
identity from the actual tensor PDE and proves both useful scaled flux bounds. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal Topology ContDiff RealInnerProductSpace
namespace HartreeF.Paper121Lemma38
open EnergySpace LocalChargeBridge LocalDualSource LocalChargeRigidity
open CompactPDEDualBridge ForcingDomain SobolevStretch StationarySelfTest
open CutoffApproximation HartreeMildPDEProducer MaximalTrajectory
attribute [local instance] energyRealSpace energyDualComplexNorm energyDualRealNorm
  energyDualComplexSpace energyDualRealSpace

/-- The PDE multiplier associated to the charge `integral zeta^2 |u|^2`. -/
def squareCutoff (zeta : V → ℝ) (x : V) : ℝ := zeta x ^ 2

theorem squareCutoff_smooth {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) :
    ContDiff ℝ (⊤ : ℕ∞) (squareCutoff zeta) := by
  have he : squareCutoff zeta = zeta * zeta := by
    ext x
    simp only [squareCutoff, Pi.mul_apply, pow_two]
  rw [he]
  exact hzeta.mul hzeta

theorem squareCutoff_compact {zeta : V → ℝ} (hc : HasCompactSupport zeta) :
    HasCompactSupport (squareCutoff zeta) := by
  have he : squareCutoff zeta = zeta * zeta := by
    ext x
    simp only [squareCutoff, Pi.mul_apply, pow_two]
  rw [he]
  exact hc.mul_left

/-- Mixed integrand representing the bounded quadratic charge form. -/
def localizedChargeIntegrand (zeta : V → ℝ) (u w : EnergyState) (x : V) : ℂ :=
  ((zeta x ^ 2 : ℝ) : ℂ) * energyValue u x * star (energyValue w x)

theorem localizedValue_pair_ae {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    (u w : EnergyState) :
    (fun x : V => localizedValue hzeta hc u x * star (localizedValue hzeta hc w x))
      =ᵐ[volume] localizedChargeIntegrand zeta u w := by
  filter_upwards [localizedValue_ae hzeta hc u, localizedValue_ae hzeta hc w]
    with x hu hw
  rw [hu, hw]
  simp only [localizedChargeIntegrand, Complex.real_smul, Complex.star_def, map_mul,
    Complex.conj_ofReal]
  push_cast
  ring

theorem localizedChargeIntegrand_integrable {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    (u w : EnergyState) : Integrable (localizedChargeIntegrand zeta u w) volume :=
  (spatialPair_integrable (localizedValue hzeta hc u) (localizedValue hzeta hc w)).congr
    (localizedValue_pair_ae hzeta hc u w)

/-- The actual bounded form is exactly the literal mixed spatial integral. -/
theorem localizedChargeForm_eq_integral {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    (u w : EnergyState) :
    localizedChargeForm hzeta hc u w =
      (∫ x : V, localizedChargeIntegrand zeta u w x).re := by
  change inner ℝ (localizedValue hzeta hc u) (localizedValue hzeta hc w) = _
  rw [real_inner_spatialPair, spatialPair_eq_integral,
    integral_congr_ae (localizedValue_pair_ae hzeta hc u w)]

/-- Identification with the exact compact test carrying multiplier `zeta^2`. -/
theorem localizedChargeForm_eq_compactConjugateTest {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    (u : EnergyState) (phi : Test) :
    localizedChargeForm hzeta hc u (schwartzEnergyState phi) =
      (energyDistribution u (compactConjugateTest
        (squareCutoff_smooth hzeta) (squareCutoff_compact hc) phi)).re := by
  rw [localizedChargeForm_eq_integral,
    energyDistribution_compactConjugateTest]
  rfl

/-- The real dual supplied by the PDE with the exact multiplier `zeta^2`. -/
def squarePDEDual {alpha c : ℝ} {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    (hH : OrdinaryHLS alpha c) : EnergyState → (EnergyState →L[ℝ] ℝ) :=
  actualPDEDual (squareCutoff_smooth hzeta) (squareCutoff_compact hc) hH

theorem squarePDEDual_continuous {alpha c : ℝ} {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    (hH : OrdinaryHLS alpha c) : Continuous (squarePDEDual hzeta hc hH) :=
  actualPDEDual_continuous (squareCutoff_smooth hzeta) (squareCutoff_compact hc) hH

/-- The actual compact Hartree PDE supplies the norm-dual derivative for an
arbitrary smooth compact cutoff, not only the repository's standard bump. -/
theorem localizedChargeForm_hasDerivAt_of_compactPDE
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {t : ℝ} (ht : t ∈ S) :
    HasDerivAt (fun s => localizedChargeForm hzeta hc (u s))
      (squarePDEDual hzeta hc hH (u t)) t := by
  apply DenseDualTime.hasDerivAt_of_dense_weak_tests (schwartzEnergyState_denseRange hDensity hSob)
    hS ((localizedChargeForm hzeta hc).continuous.comp_continuousOn hu)
    ((squarePDEDual_continuous hzeta hc hH).comp_continuousOn hu) _ ht
  intro eta heta hetaCompact hetaSupport phi
  change (∫ t, deriv eta t *
      localizedChargeForm hzeta hc (u t) (schwartzEnergyState phi)) =
    -(∫ t, eta t * squarePDEDual hzeta hc hH (u t) (schwartzEnergyState phi))
  have he := real_weak_identity_of_tensor hH hu hp heta hetaCompact hetaSupport
    (compactConjugateTest (squareCutoff_smooth hzeta) (squareCutoff_compact hc) phi)
    (compactConjugateTest_compact
      (squareCutoff_smooth hzeta) (squareCutoff_compact hc) phi)
  simpa only [localizedChargeForm_eq_compactConjugateTest hzeta hc,
    squarePDEDual, actualPDEDual_eq_distribution, stateTest, spatialTest] using he

/-- Exact localized charge derivative and flux formula for arbitrary `zeta`. -/
theorem localized_square_charge_derivative_flux
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {t : ℝ} (ht : t ∈ S) :
    HasDerivAt (fun s => ∫ x : V, zeta x ^ 2 * ‖energyValue (u s) x‖ ^ 2)
      (2 * ∑ j : Fin 3, (∫ x : V,
        fluxIntegrand (χ := squareCutoff zeta) (u t) j x).im) t := by
  have hd := localized_square_charge_hasDerivAt hzeta hc
    (hu.continuousAt (hS.mem_nhds ht))
    (localizedChargeForm_hasDerivAt_of_compactPDE
      hDensity hSob hH hzeta hc hS hu hp ht)
  simpa only [squarePDEDual, actualPDEDual_diagonal_flux] using hd

/-- The localized charge is genuinely C1 on the open solution domain. -/
theorem localized_square_charge_contDiffOn
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) :
    ContDiffOn ℝ 1
      (fun s => ∫ x : V, zeta x ^ 2 * ‖energyValue (u s) x‖ ^ 2) S := by
  let Q := fun s : ℝ => ∫ x : V, zeta x ^ 2 * ‖energyValue (u s) x‖ ^ 2
  let F := fun s : ℝ => 2 * squarePDEDual hzeta hc hH (u s) (u s)
  have hd : ∀ t ∈ S, HasDerivAt Q (F t) t := by
    intro t ht
    have hraw := localized_square_charge_hasDerivAt hzeta hc
      (hu.continuousAt (hS.mem_nhds ht))
      (localizedChargeForm_hasDerivAt_of_compactPDE
        hDensity hSob hH hzeta hc hS hu hp ht)
    simpa only [Q, F] using hraw
  have hdiag : Continuous
      (fun v : EnergyState => squarePDEDual hzeta hc hH v v) := by
    have heval : Continuous
        (fun z : (EnergyState →L[ℝ] ℝ) × EnergyState => z.1 z.2) :=
      continuous_fst.clm_apply continuous_snd
    exact heval.comp ((squarePDEDual_continuous hzeta hc hH).prodMk continuous_id)
  have hF : ContinuousOn F S := by
    exact continuous_const.continuousOn.mul (hdiag.comp_continuousOn hu)
  apply (contDiffOn_one_iff_derivWithin hS.uniqueDiffOn).2
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, ?_⟩
  refine hF.congr ?_
  intro t ht
  rw [derivWithin_of_isOpen hS ht, (hd t ht).deriv]

/-- The manuscript's rescaled cutoff `zeta_R(x)=zeta(x/R)`. -/
def scaledCutoff (zeta : V → ℝ) (R : ℝ) (x : V) : ℝ := zeta (R⁻¹ • x)

theorem scaledCutoff_smooth {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledCutoff zeta R) :=
  hzeta.comp (contDiff_id.const_smul R⁻¹)

theorem scaledCutoff_compact {zeta : V → ℝ} (hc : HasCompactSupport zeta)
    {R : ℝ} (hR : 0 < R) : HasCompactSupport (scaledCutoff zeta R) := by
  exact hc.comp_smul (inv_ne_zero hR.ne')

/-- The multiplier whose gradient appears in the local charge flux. -/
def scaledSquareCutoff (zeta : V → ℝ) (R : ℝ) : V → ℝ :=
  squareCutoff (scaledCutoff zeta R)

theorem scaledSquareCutoff_smooth {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledSquareCutoff zeta R) :=
  squareCutoff_smooth (scaledCutoff_smooth hzeta R)

theorem scaledSquareCutoff_compact {zeta : V → ℝ} (hc : HasCompactSupport zeta)
    {R : ℝ} (hR : 0 < R) : HasCompactSupport (scaledSquareCutoff zeta R) :=
  squareCutoff_compact (scaledCutoff_compact hc hR)

theorem scaledSquareCutoff_gradient {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (R : ℝ) (x : V) :
    gradient (scaledSquareCutoff zeta R) x =
      R⁻¹ • gradient (squareCutoff zeta) (R⁻¹ • x) := by
  exact gradient_comp_smul
    ((squareCutoff_smooth hzeta).differentiable (by simp)) R⁻¹ x

/-- The critical L3 gradient size of the unscaled squared cutoff. -/
def squareGradientL3Norm (zeta : V → ℝ) : ℝ :=
  (eLpNorm (gradient (squareCutoff zeta)) 3 volume).toReal

theorem squareGradientL3Norm_nonneg (zeta : V → ℝ) :
    0 ≤ squareGradientL3Norm zeta := ENNReal.toReal_nonneg

theorem squareGradientL3Norm_lt_top {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) :
    eLpNorm (gradient (squareCutoff zeta)) 3 volume < (∞ : ℝ≥0∞) :=
  (WeakCutoffLp.cutoff_gradient_memLp
    (squareCutoff_smooth hzeta) (squareCutoff_compact hc) 3).eLpNorm_lt_top

/-- Critical L3 scaling is exactly radius independent for an arbitrary cutoff. -/
theorem scaledSquareCutoff_gradient_eLpNorm {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) {R : ℝ} (hR : 0 < R) :
    eLpNorm (gradient (scaledSquareCutoff zeta R)) 3 volume =
      eLpNorm (gradient (squareCutoff zeta)) 3 volume := by
  have he : gradient (scaledSquareCutoff zeta R) = fun x =>
      R⁻¹ • gradient (squareCutoff zeta) (R⁻¹ • x) :=
    funext (scaledSquareCutoff_gradient hzeta R)
  rw [he]
  exact eLpNorm_scale_critical_three
    (WeakCutoffLp.cutoff_gradient_continuous
      (squareCutoff_smooth hzeta)).aestronglyMeasurable (inv_pos.mpr hR)

/-- Each coordinate coefficient is controlled by the full, scale-invariant L3 norm. -/
theorem scaledSquareCutoff_coefficientLp_norm {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {R : ℝ} (hR : 0 < R) (j : Fin 3) :
    ‖coefficientLp
      (coefficientDerivative_continuous (scaledSquareCutoff_smooth hzeta R) j)
      (coefficientDerivative_compact (scaledSquareCutoff_compact hc hR) j) 3‖ ≤
        squareGradientL3Norm zeta := by
  let hs := scaledSquareCutoff_smooth hzeta R
  let hsc := scaledSquareCutoff_compact hc hR
  let a := coefficientLp (coefficientDerivative_continuous hs j)
    (coefficientDerivative_compact hsc j) 3
  change ‖a‖ ≤ squareGradientL3Norm zeta
  rw [Lp.norm_def]
  apply ENNReal.toReal_mono (squareGradientL3Norm_lt_top hzeta hc).ne
  calc
    eLpNorm (a : V → ℂ) 3 volume ≤
        eLpNorm (gradient (scaledSquareCutoff zeta R)) 3 volume := by
      apply eLpNorm_mono_ae (Lp.aestronglyMeasurable a)
      filter_upwards [coefficientLp_ae (coefficientDerivative_continuous hs j)
        (coefficientDerivative_compact hsc j) 3] with x hx
      change a x = _ at hx
      rw [hx, Complex.norm_real, coefficientDerivative_eq_gradient_coordinate]
      exact PiLp.norm_apply_le _ _
    _ = eLpNorm (gradient (squareCutoff zeta)) 3 volume :=
      scaledSquareCutoff_gradient_eLpNorm hzeta hR

/-- Radius-independent constant for the pre-L2 flux estimate. -/
def preL2ChargeFluxConstant (K : ℝ) (zeta : V → ℝ) : ℝ :=
  6 * squareGradientL3Norm zeta * K ^ ((6 : ℝ)⁻¹)

theorem preL2ChargeFluxConstant_nonneg {K : ℝ} (hSob : OrdinarySobolev K)
    (zeta : V → ℝ) : 0 ≤ preL2ChargeFluxConstant K zeta := by
  unfold preL2ChargeFluxConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (squareGradientL3Norm_nonneg zeta))
    (Real.rpow_nonneg hSob.nonneg _)

/-- First useful flux estimate: no L2 value hypothesis, and no radius loss. -/
theorem scaledSquareFlux_preL2_bound {K : ℝ} (hSob : OrdinarySobolev K)
    {zeta : V → ℝ} (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (hc : HasCompactSupport zeta) {R : ℝ} (hR : 0 < R) (u : EnergyState) :
    |2 * ∑ j : Fin 3, (∫ x : V,
      fluxIntegrand (χ := scaledSquareCutoff zeta R) u j x).im| ≤
        preL2ChargeFluxConstant K zeta * pureGradientNorm u ^ 2 := by
  have hcoord (j : Fin 3) :
      |(∫ x : V, fluxIntegrand (χ := scaledSquareCutoff zeta R) u j x).im| ≤
        squareGradientL3Norm zeta * K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u ^ 2 := by
    calc
      _ ≤ ‖coefficientLp
          (coefficientDerivative_continuous (scaledSquareCutoff_smooth hzeta R) j)
          (coefficientDerivative_compact (scaledSquareCutoff_compact hc hR) j) 3‖ *
          ‖energyValue u‖ * ‖energyGradient j u‖ :=
        originalFlux_coordinate_le_coefficient
          (scaledSquareCutoff_smooth hzeta R) (scaledSquareCutoff_compact hc hR) u j
      _ ≤ (squareGradientL3Norm zeta *
          (K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u)) * pureGradientNorm u := by
        apply mul_le_mul
        · exact mul_le_mul (scaledSquareCutoff_coefficientLp_norm hzeta hc hR j)
            (energyValue_le_pureGradient hSob u) (norm_nonneg _)
            (squareGradientL3Norm_nonneg zeta)
        · exact energyGradient_le_pureGradient u j
        · exact norm_nonneg _
        · exact mul_nonneg (squareGradientL3Norm_nonneg zeta)
            (mul_nonneg (Real.rpow_nonneg hSob.nonneg _) (pureGradientNorm_nonneg u))
      _ = _ := by ring
  calc
    _ = 2 * |∑ j : Fin 3, (∫ x : V,
        fluxIntegrand (χ := scaledSquareCutoff zeta R) u j x).im| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ∑ j : Fin 3, |(∫ x : V,
        fluxIntegrand (χ := scaledSquareCutoff zeta R) u j x).im| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2 * ∑ _j : Fin 3,
        (squareGradientL3Norm zeta * K ^ ((6 : ℝ)⁻¹) * pureGradientNorm u ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hcoord j)) (by norm_num)
    _ = preL2ChargeFluxConstant K zeta * pureGradientNorm u ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        preL2ChargeFluxConstant]
      ring

/-- A finite pointwise bound for the gradient of the unscaled squared cutoff. -/
theorem exists_squareGradientBound {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V, ‖gradient (squareCutoff zeta) x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (WeakCutoffLp.cutoff_gradient_continuous (squareCutoff_smooth hzeta)).bounded_above_of_compact_support
      (WeakCutoffLp.cutoff_gradient_hasCompactSupport (squareCutoff_compact hc))
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

def squareGradientBound {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) : ℝ :=
  (exists_squareGradientBound hzeta hc).choose

theorem squareGradientBound_nonneg {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) :
    0 ≤ squareGradientBound hzeta hc :=
  (exists_squareGradientBound hzeta hc).choose_spec.1

theorem squareGradientBound_spec {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) (x : V) :
    ‖gradient (squareCutoff zeta) x‖ ≤ squareGradientBound hzeta hc :=
  (exists_squareGradientBound hzeta hc).choose_spec.2 x

theorem scaledSquareCutoff_gradient_bound {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {R : ℝ} (hR : 0 < R) (x : V) :
    ‖gradient (scaledSquareCutoff zeta R) x‖ ≤ squareGradientBound hzeta hc / R := by
  rw [scaledSquareCutoff_gradient hzeta R, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hR)]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left (squareGradientBound_spec hzeta hc (R⁻¹ • x))
      (inv_nonneg.mpr hR.le)

/-- Generic exact L2 flux estimate from a pointwise cutoff-gradient bound. -/
theorem flux_l2_bound_of_gradient_bound {chi : V → ℝ}
    (hchi : ContDiff ℝ (⊤ : ℕ∞) chi) (hc : HasCompactSupport chi)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x : V, ‖gradient chi x‖ ≤ C)
    (u : EnergyState) (v : L2) (hSame : (v : V → ℂ) =ᵐ[volume] energyValue u) :
    |∑ j : Fin 3, (∫ x : V, fluxIntegrand (χ := chi) u j x).im| ≤
      C * ‖v‖ * pureGradientNorm u := by
  let G := contractedGradientL2 hchi hc u
  have hG : ‖G‖ ≤ C * pureGradientNorm u :=
    contractedGradientL2_norm hchi hc hC hbound u
  have he : (∑ j : Fin 3,
      (∫ x : V, fluxIntegrand (χ := chi) u j x).im) = (inner ℂ v G).im := by
    change (∑ j : Fin 3, Complex.imCLM
      (∫ x : V, fluxIntegrand (χ := chi) u j x)) = Complex.imCLM (inner ℂ v G)
    rw [← map_sum, originalFlux_sum_eq_inner hchi hc u v hSame]
  rw [he]
  calc
    |(inner ℂ v G).im| ≤ ‖inner ℂ v G‖ := Complex.abs_im_le_norm _
    _ ≤ ‖v‖ * ‖G‖ := norm_inner_le_norm (𝕜 := ℂ) v G
    _ ≤ ‖v‖ * (C * pureGradientNorm u) :=
      mul_le_mul_of_nonneg_left hG (norm_nonneg v)
    _ = C * ‖v‖ * pureGradientNorm u := by ring

/-- Constant in the sharper post-L2 estimate. -/
def l2ChargeFluxConstant {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) : ℝ :=
  2 * squareGradientBound hzeta hc

theorem l2ChargeFluxConstant_nonneg {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) :
    0 ≤ l2ChargeFluxConstant hzeta hc := by
  exact mul_nonneg (by norm_num) (squareGradientBound_nonneg hzeta hc)

/-- Second useful flux estimate: after an L2 representative exists, it gains `R^-1`. -/
theorem scaledSquareFlux_l2_bound {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {R : ℝ} (hR : 0 < R) (u : EnergyState) (v : L2)
    (hSame : (v : V → ℂ) =ᵐ[volume] energyValue u) :
    |2 * ∑ j : Fin 3, (∫ x : V,
      fluxIntegrand (χ := scaledSquareCutoff zeta R) u j x).im| ≤
      (l2ChargeFluxConstant hzeta hc / R) * ‖v‖ * pureGradientNorm u := by
  have hbase := flux_l2_bound_of_gradient_bound
    (scaledSquareCutoff_smooth hzeta R) (scaledSquareCutoff_compact hc hR)
    (div_nonneg (squareGradientBound_nonneg hzeta hc) hR.le)
    (scaledSquareCutoff_gradient_bound hzeta hc hR) u v hSame
  calc
    _ = 2 * |∑ j : Fin 3, (∫ x : V,
        fluxIntegrand (χ := scaledSquareCutoff zeta R) u j x).im| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ((squareGradientBound hzeta hc / R) * ‖v‖ * pureGradientNorm u) :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = (l2ChargeFluxConstant hzeta hc / R) * ‖v‖ * pureGradientNorm u := by
      unfold l2ChargeFluxConstant
      ring

/-- One cutoff-dependent constant that works for both manuscript estimates. -/
def chargeFluxConstant (K : ℝ) (zeta : V → ℝ)
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta) : ℝ :=
  max (preL2ChargeFluxConstant K zeta) (l2ChargeFluxConstant hzeta hc)

theorem chargeFluxConstant_nonneg {K : ℝ} (hSob : OrdinarySobolev K)
    {zeta : V → ℝ} (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (hc : HasCompactSupport zeta) : 0 ≤ chargeFluxConstant K zeta hzeta hc :=
  (preL2ChargeFluxConstant_nonneg hSob zeta).trans (le_max_left _ _)

/-- Exact derivative formula for the scaled cutoff used by both estimates. -/
theorem scaled_localized_charge_derivative_flux
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {R t : ℝ} (hR : 0 < R) (ht : t ∈ S) :
    HasDerivAt
      (fun s => ∫ x : V,
        scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2)
      (2 * ∑ j : Fin 3, (∫ x : V,
        fluxIntegrand (χ := scaledSquareCutoff zeta R) (u t) j x).im) t := by
  simpa only [scaledSquareCutoff] using
    localized_square_charge_derivative_flux hDensity hSob hH
      (scaledCutoff_smooth hzeta R) (scaledCutoff_compact hc hR) hS hu hp ht

theorem scaled_localized_charge_contDiffOn
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ 1
      (fun s => ∫ x : V,
        scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) S :=
  localized_square_charge_contDiffOn hDensity hSob hH
    (scaledCutoff_smooth hzeta R) (scaledCutoff_compact hc hR) hS hu hp

/-- Derivative form of the radius-uniform pre-L2 estimate. -/
theorem scaled_localized_charge_deriv_preL2_bound
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {R t : ℝ} (hR : 0 < R) (ht : t ∈ S) :
    |deriv (fun s => ∫ x : V,
      scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) t| ≤
      chargeFluxConstant K zeta hzeta hc * pureGradientNorm (u t) ^ 2 := by
  rw [(scaled_localized_charge_derivative_flux
    hDensity hSob hH hzeta hc hS hu hp hR ht).deriv]
  exact (scaledSquareFlux_preL2_bound hSob hzeta hc hR (u t)).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

/-- Derivative form of the sharper post-L2 `R^-1` estimate. -/
theorem scaled_localized_charge_deriv_l2_bound
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) {R t : ℝ} (hR : 0 < R) (ht : t ∈ S)
    (v : L2) (hSame : (v : V → ℂ) =ᵐ[volume] energyValue (u t)) :
    |deriv (fun s => ∫ x : V,
      scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) t| ≤
      (chargeFluxConstant K zeta hzeta hc / R) * ‖v‖ * pureGradientNorm (u t) := by
  rw [(scaled_localized_charge_derivative_flux
    hDensity hSob hH hzeta hc hS hu hp hR ht).deriv]
  have hbase := scaledSquareFlux_l2_bound hzeta hc hR (u t) v hSame
  refine hbase.trans ?_
  have hdiv : l2ChargeFluxConstant hzeta hc / R ≤
      chargeFluxConstant K zeta hzeta hc / R :=
    div_le_div_of_nonneg_right (le_max_right _ _) hR.le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdiv (norm_nonneg v)) (pureGradientNorm_nonneg (u t))

/-- The uniform `C_zeta B^2` form stated in the manuscript. -/
theorem scaled_localized_charge_deriv_uniform_gradient_bound
    (hDensity : OrdinaryH1Density) {K alpha c B : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) (hB : ∀ t ∈ S, pureGradientNorm (u t) ≤ B)
    {R t : ℝ} (hR : 0 < R) (ht : t ∈ S) :
    |deriv (fun s => ∫ x : V,
      scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) t| ≤
      chargeFluxConstant K zeta hzeta hc * B ^ 2 := by
  have hpnt := scaled_localized_charge_deriv_preL2_bound
    hDensity hSob hH hzeta hc hS hu hp hR ht
  have hsq : pureGradientNorm (u t) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (pureGradientNorm_nonneg (u t)) (hB t ht) 2
  exact hpnt.trans (mul_le_mul_of_nonneg_left hsq
    (chargeFluxConstant_nonneg hSob hzeta hc))

/-- Compact-interval version of the manuscript's post-L2 estimate.  The family
`v` records the separately available L2 representative at each time. -/
theorem scaled_localized_charge_deriv_uniform_l2_bound_on_Icc
    (hDensity : OrdinaryH1Density) {K alpha c a b B M : ℝ}
    (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    {zeta : V → ℝ} (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (hc : HasCompactSupport zeta) {u : ℝ → EnergyState} {S : Set ℝ}
    (hS : IsOpen S) (hu : ContinuousOn u S) (hp : CompactHartreeTensorPDE hH u S)
    (hI : Icc a b ⊆ S) (v : ℝ → L2)
    (hSame : ∀ t ∈ Icc a b, (v t : V → ℂ) =ᵐ[volume] energyValue (u t))
    (hM : ∀ t ∈ Icc a b, ‖v t‖ ≤ M)
    (hB0 : 0 ≤ B) (hB : ∀ t ∈ Icc a b, pureGradientNorm (u t) ≤ B)
    {R t : ℝ} (hR : 0 < R) (ht : t ∈ Icc a b) :
    |deriv (fun s => ∫ x : V,
      scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) t| ≤
      (chargeFluxConstant K zeta hzeta hc / R) * M * B := by
  have hpnt := scaled_localized_charge_deriv_l2_bound
    hDensity hSob hH hzeta hc hS hu hp hR (hI ht) (v t) (hSame t ht)
  have hCR : 0 ≤ chargeFluxConstant K zeta hzeta hc / R :=
    div_nonneg (chargeFluxConstant_nonneg hSob hzeta hc) hR.le
  calc
    _ ≤ (chargeFluxConstant K zeta hzeta hc / R) * ‖v t‖ *
        pureGradientNorm (u t) := hpnt
    _ ≤ (chargeFluxConstant K zeta hzeta hc / R) * ‖v t‖ * B :=
      mul_le_mul_of_nonneg_left (hB t ht)
        (mul_nonneg hCR (norm_nonneg (v t)))
    _ ≤ (chargeFluxConstant K zeta hzeta hc / R) * M * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hM t ht) hCR) hB0

/-- Full Lemma 3.8: C1 local charge, exact flux identity, and both scaled bounds. -/
theorem lemma38_local_charge_and_two_flux_bounds
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) :
    ContDiffOn ℝ 1
      (fun s => ∫ x : V, zeta x ^ 2 * ‖energyValue (u s) x‖ ^ 2) S ∧
    (∀ t ∈ S, HasDerivAt
      (fun s => ∫ x : V, zeta x ^ 2 * ‖energyValue (u s) x‖ ^ 2)
      (2 * ∑ j : Fin 3, (∫ x : V,
        fluxIntegrand (χ := squareCutoff zeta) (u t) j x).im) t) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (R : ℝ), 0 < R → ∀ t ∈ S,
        |deriv (fun s => ∫ x : V,
          scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) t| ≤
          C * pureGradientNorm (u t) ^ 2) ∧
      ∀ (R : ℝ), 0 < R → ∀ t ∈ S, ∀ v : L2,
        (v : V → ℂ) =ᵐ[volume] energyValue (u t) →
        |deriv (fun s => ∫ x : V,
          scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) t| ≤
          (C / R) * ‖v‖ * pureGradientNorm (u t) := by
  refine ⟨localized_square_charge_contDiffOn hDensity hSob hH hzeta hc hS hu hp,
    fun t ht => localized_square_charge_derivative_flux
      hDensity hSob hH hzeta hc hS hu hp ht,
    chargeFluxConstant K zeta hzeta hc, chargeFluxConstant_nonneg hSob hzeta hc, ?_, ?_⟩
  · intro R hR t ht
    exact scaled_localized_charge_deriv_preL2_bound
      hDensity hSob hH hzeta hc hS hu hp hR ht
  · intro R hR t ht v hSame
    exact scaled_localized_charge_deriv_l2_bound
      hDensity hSob hH hzeta hc hS hu hp hR ht v hSame

/-- Named conclusion package used to instantiate Lemma 3.8 on the constructed
actual maximal mild trajectory without adding a PDE premise to that corollary. -/
def LocalChargeAndFluxBounds (zeta : V → ℝ)
    (u : ℝ → EnergyState) (S : Set ℝ) : Prop :=
  ContDiffOn ℝ 1
      (fun s => ∫ x : V, zeta x ^ 2 * ‖energyValue (u s) x‖ ^ 2) S ∧
    (∀ t ∈ S, HasDerivAt
      (fun s => ∫ x : V, zeta x ^ 2 * ‖energyValue (u s) x‖ ^ 2)
      (2 * ∑ j : Fin 3, (∫ x : V,
        fluxIntegrand (χ := squareCutoff zeta) (u t) j x).im) t) ∧
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (R : ℝ), 0 < R → ∀ t ∈ S,
        |deriv (fun s => ∫ x : V,
          scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) t| ≤
          C * pureGradientNorm (u t) ^ 2) ∧
      ∀ (R : ℝ), 0 < R → ∀ t ∈ S, ∀ v : L2,
        (v : V → ℂ) =ᵐ[volume] energyValue (u t) →
        |deriv (fun s => ∫ x : V,
          scaledCutoff zeta R x ^ 2 * ‖energyValue (u s) x‖ ^ 2) t| ≤
          (C / R) * ‖v‖ * pureGradientNorm (u t)

theorem localChargeAndFluxBounds_of_compactPDE
    (hDensity : OrdinaryH1Density) {K alpha c : ℝ} (hSob : OrdinarySobolev K)
    (hH : OrdinaryHLS alpha c) {zeta : V → ℝ}
    (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta) (hc : HasCompactSupport zeta)
    {u : ℝ → EnergyState} {S : Set ℝ} (hS : IsOpen S) (hu : ContinuousOn u S)
    (hp : CompactHartreeTensorPDE hH u S) :
    LocalChargeAndFluxBounds zeta u S := by
  exact lemma38_local_charge_and_two_flux_bounds
    hDensity hSob hH hzeta hc hS hu hp

/-- Direct specialization to the repository's constructed actual maximal
solution.  Its tensor PDE is produced from its genuine mild formula. -/
theorem lemma38_actualMaximalTrajectory
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : Retarded.OrdinaryEndpointBound C0)
    (hfree : ActualStrichartz.OrdinaryHomogeneousStrichartz Ch)
    (hret : ActualStrichartz.OrdinaryRetardedStrichartz h0 Cr)
    (hefree : EndpointOutput.OrdinaryHomogeneousEndpointOutput Che)
    (heret : EndpointOutput.OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hgen : LinearWeakEquation.OrdinaryFreeDistributionScalarGenerator)
    {zeta : V → ℝ} (hzeta : ContDiff ℝ (⊤ : ℕ∞) zeta)
    (hc : HasCompactSupport zeta) (s0 : ℝ) (u0 : EnergyState) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret
      hefree heret hH s0 u0
    LocalChargeAndFluxBounds zeta M.state M.domain := by
  dsimp only
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret
    hefree heret hH s0 u0
  change LocalChargeAndFluxBounds zeta M.state M.domain
  exact localChargeAndFluxBounds_of_compactPDE hDensity hSob hH hzeta hc
    M.domain_open M.continuous
    (localMildTrajectory_domain_tensorPDE hDensity hSob hH h0 hfree hret hgen M)

#print axioms lemma38_local_charge_and_two_flux_bounds
#print axioms lemma38_actualMaximalTrajectory

end HartreeF.Paper121Lemma38

