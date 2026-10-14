import FRealPairingBounds
import FRegularizedSourceRepresentatives
import FActualRegularizedEnergyFTC
import FRegularizedLaplacianL2
import FRegularizedKineticCancellation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv Laplacian
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open WeakSourcePairing RegularizedEnergyPairing StateEnergy ForcingDomain ForcingContinuity
attribute [local instance] canonicalEnergyNormedSpace
attribute [local irreducible] energyValue

local instance : ENNReal.HolderConjugate sourceExponent 6 := by
  have h : Real.HolderTriple (6/5) 6 1 := by constructor <;> norm_num
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

theorem source_complex_pair_integrable (f : SourceLp) (h : L6) :
    Integrable (fun x => f x * star (h x)) volume := by
  have hi := (Lp.memLp f).integrable_mul (Lp.memLp (conjugateL6 h))
  apply hi.congr
  filter_upwards [conjugateL6_coeFn h] with x hx
  simp only [Pi.mul_apply, hx]

theorem sourceIPair_complex (f : SourceLp) (h : L6) :
    sourceIPair f h = (Complex.I * ∫ x, f x * star (h x)).re := by
  rw [sourceIPair_integral, ← integral_const_mul]
  change _ = RCLike.re (∫ x, Complex.I * (f x * star (h x)))
  rw [← integral_re ((source_complex_pair_integrable f h).const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [real_inner_eq_re_inner ℂ]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  congr 1
  ring

theorem sourceIPair_l2 (f : SourceLp) (h : L6) (f2 h2 : EnergySpace.L2)
    (hf : (f : V → ℂ) =ᵐ[volume] f2) (hh : (h : V → ℂ) =ᵐ[volume] h2) :
    sourceIPair f h = inner ℝ h2 (Complex.I • f2) := by
  rw [sourceIPair_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, hh, Lp.coeFn_smul Complex.I f2] with x hfx hhx hIx
  simp only [hfx, hhx, hIx, Pi.smul_apply, smul_eq_mul]

theorem l2IPair_skew (f g : EnergySpace.L2) :
    inner ℝ f (Complex.I • g) = -inner ℝ g (Complex.I • f) := by
  rw [l2_real_inner_eq_re, l2_real_inner_eq_re, inner_smul_right, inner_smul_right]
  have hc := congrArg Complex.im (inner_conj_symm f g)
  simp only [Complex.conj_im] at hc
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  linarith

theorem l2IPair_self (f : EnergySpace.L2) : inner ℝ f (Complex.I • f) = 0 := by
  have h := l2IPair_skew f f
  linarith

theorem deltaJ_eq_sum_second (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState) :
    deltaJ hDensity hSob n u =
      ∑ j : Fin 3, (secondCutoff n j j).energyCLM hDensity hSob u := by
  apply energyDistribution_injective
  rw [map_sum, deltaJ_distribution]
  rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin 3) ℝ)]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [EuclideanSpace.basisFun_apply, coordinate] using
    ((J_first_two_derivatives hDensity hSob n u).2 j j).symm

/-- Actual integration by parts against ΔJ_n u, obtained from the exact
Schwartz derivative limits and both canonical source derivatives. -/
theorem regularized_source_laplacian_pair (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : EnergyState)
    (f : SourceLp) (g : Fin 3 → SourceLp) (f2 : EnergySpace.L2)
    (hf2 : (f : V → ℂ) =ᵐ[volume] f2)
    (hfg : ∀ j, ∂_{coordinate j} (Lp.toTemperedDistribution f) =
      Lp.toTemperedDistribution (g j)) :
    inner ℝ f2 (Complex.I • deltaJValueL2 n u) =
      ∑ j : Fin 3, sourceIPair (g j)
        (energyValue ((firstCutoff n j).energyCLM hDensity hSob u)) := by
  have hj (j : Fin 3) : sourceIPair f
      (energyValue ((secondCutoff n j j).energyCLM hDensity hSob u)) =
      -sourceIPair (g j) (energyValue ((firstCutoff n j).energyCLM hDensity hSob u)) := by
    rw [sourceIPair_complex, sourceIPair_complex,
      regularized_conjugate_source_integration_by_parts hDensity hSob n u j j f (g j) (hfg j)]
    simp only [mul_neg, Complex.neg_re]
  have hs : sourceIPair f (energyValue (deltaJ hDensity hSob n u)) =
      -(∑ j : Fin 3, sourceIPair (g j)
        (energyValue ((firstCutoff n j).energyCLM hDensity hSob u))) := by
    rw [deltaJ_eq_sum_second, map_sum, map_sum]
    simp only [hj, Finset.sum_neg_distrib]
  rw [sourceIPair_l2 f _ f2 (deltaJValueL2 n u) hf2
    (deltaJ_value_ae hDensity hSob n u)] at hs
  rw [l2IPair_skew]
  linarith

section RealDerivative
/-- An explicit derivative formula for the existing totalEnergy functional. -/
theorem totalEnergy_fderiv_apply {alpha : ℝ}
    (hH : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (u du : EnergyState) :
    fderiv ℝ (totalEnergy alpha) u du =
      (∑ j : Fin 3, inner ℝ (energyGradient j u) (energyGradient j du)) -
        (∫ x, star (forcing alpha (HeatRiesz.standardRieszConstant alpha)
          (energyValue u) x) * energyValue du x).re := by
  have hd := ((hasDerivAt_id (0 : ℝ)).smul_const du).const_add u
  have h1 := totalEnergy_curve_hasDerivAt hH hd
  have h2 := ((totalEnergy_contDiff hH).differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hd
  simpa only [id_eq, one_smul, zero_smul, add_zero] using h2.unique h1

end RealDerivative

/-- The remaining potential term is the actual L2 inner product whenever
its produced nonlinear and regularized vector-field L2 values are used. -/
theorem forcing_energy_pair_l2 {alpha c : ℝ} (u du : EnergyState)
    (N d : EnergySpace.L2)
    (hN : forcing alpha c (energyValue u) =ᵐ[volume] N)
    (hd : (energyValue du : V → ℂ) =ᵐ[volume] d) :
    (∫ x, star (forcing alpha c (energyValue u) x) * energyValue du x).re =
      inner ℝ N d := by
  rw [l2_real_inner_eq_re, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hN, hd] with x hNx hdx
  simp only [hNx, hdx, RCLike.inner_apply, starRingEnd_apply]
  ring

#print axioms sourceIPair_complex
#print axioms sourceIPair_l2
#print axioms l2IPair_skew
#print axioms regularized_source_laplacian_pair
#print axioms totalEnergy_fderiv_apply
#print axioms forcing_energy_pair_l2
end HartreeF.Regularization.Actual
