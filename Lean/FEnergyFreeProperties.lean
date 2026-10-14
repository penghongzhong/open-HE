import FEnergyFreeConstruction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.EnergySpace
open SobolevStretch StationarySelfTest

theorem energyDistribution_injective : Function.Injective energyDistribution := by
  intro u v h
  apply energyValue_injective
  exact (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure V)) (p := 6))) h

variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)

theorem freeEnergyState_unique (t : ℝ) (u w : EnergyState)
    (hw : energyDistribution w = FreeFlow.free t (energyDistribution u)) :
    w = freeEnergyState hDensity hSob t u := by
  apply energyDistribution_injective
  rw [hw, freeEnergyState_distribution]

theorem freeEnergyState_schwartz (t : ℝ) (φ : Test) :
    freeEnergyState hDensity hSob t (schwartzEnergyState φ) =
      schwartzEnergyState (FreeFlow.freeSchwartz t φ) := by
  symm
  exact freeEnergyState_unique hDensity hSob t _ _ (freeSchwartz_energyDistribution t φ)

/-- Every actual approximating sequence converges to the same constructed
state after propagation; there is no dependence on the chosen sequence. -/
theorem freeEnergyState_approximation (t : ℝ) {φ : ℕ → Test} {u : EnergyState}
    (hφ : Tendsto (fun n => schwartzEnergyState (φ n)) atTop (𝓝 u)) :
    Tendsto (fun n => schwartzEnergyState (FreeFlow.freeSchwartz t (φ n))) atTop
      (𝓝 (freeEnergyState hDensity hSob t u)) := by
  apply tendsto_of_gradientTendsto hSob
  intro j
  have h := (FreeFlow.freeL2 t).continuous.tendsto (energyGradient j u) |>.comp
    ((energyGradient j).continuous.tendsto u |>.comp hφ)
  simpa only [Function.comp_def, freeSchwartz_energyGradient, freeEnergyState_gradient] using h

theorem freeEnergyState_limit_unique (t : ℝ) {φ : ℕ → Test} {u w : EnergyState}
    (hφ : Tendsto (fun n => schwartzEnergyState (φ n)) atTop (𝓝 u))
    (hw : Tendsto (fun n => schwartzEnergyState (FreeFlow.freeSchwartz t (φ n))) atTop (𝓝 w)) :
    w = freeEnergyState hDensity hSob t u :=
  tendsto_nhds_unique hw (freeEnergyState_approximation hDensity hSob t hφ)

/-- Different admissible retained Sobolev constants or density witnesses give
exactly the same full state because they produce the same literal distribution. -/
theorem freeEnergyState_independent (hDensity' : OrdinaryH1Density) {K' : ℝ}
    (hSob' : OrdinarySobolev K') (t : ℝ) (u : EnergyState) :
    freeEnergyState hDensity hSob t u = freeEnergyState hDensity' hSob' t u := by
  apply energyDistribution_injective
  rw [freeEnergyState_distribution, freeEnergyState_distribution]

theorem freeEnergyState_zero_time (u : EnergyState) :
    freeEnergyState hDensity hSob 0 u = u := by
  apply energyDistribution_injective
  rw [freeEnergyState_distribution, FreeFlow.free_zero]

theorem freeEnergyState_add_time (s t : ℝ) (u : EnergyState) :
    freeEnergyState hDensity hSob (s + t) u =
      freeEnergyState hDensity hSob s (freeEnergyState hDensity hSob t u) := by
  apply energyDistribution_injective
  simp only [freeEnergyState_distribution, FreeFlow.free_add]

theorem freeEnergyState_inverse (t : ℝ) (u : EnergyState) :
    freeEnergyState hDensity hSob t (freeEnergyState hDensity hSob (-t) u) = u := by
  rw [← freeEnergyState_add_time, add_neg_cancel, freeEnergyState_zero_time]

theorem freeEnergyState_add (t : ℝ) (u v : EnergyState) :
    freeEnergyState hDensity hSob t (u + v) =
      freeEnergyState hDensity hSob t u + freeEnergyState hDensity hSob t v := by
  apply energyDistribution_injective
  simp only [freeEnergyState_distribution, map_add]

theorem freeEnergyState_smul (t : ℝ) (c : ℂ) (u : EnergyState) :
    freeEnergyState hDensity hSob t (c • u) = c • freeEnergyState hDensity hSob t u := by
  apply energyDistribution_injective
  simp only [freeEnergyState_distribution, map_smul]

theorem freeEnergyState_gradientSquared (t : ℝ) (u : EnergyState) :
    gradientSquared (freeEnergyState hDensity hSob t u) = gradientSquared u := by
  simp only [gradientSquared, freeEnergyState_gradient, FreeFlow.freeL2_norm]

/-- Pure gradient norm preservation, not nonlinear Hartree energy preservation. -/
theorem freeEnergyState_pureGradientNorm (t : ℝ) (u : EnergyState) :
    pureGradientNorm (freeEnergyState hDensity hSob t u) = pureGradientNorm u := by
  simp only [pureGradientNorm, freeEnergyState_gradientSquared]

theorem freeEnergyState_norm_bound (t : ℝ) (u : EnergyState) :
    ‖freeEnergyState hDensity hSob t u‖ ≤
      (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) * ‖u‖ := by
  calc
    _ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm (freeEnergyState hDensity hSob t u) :=
      energyState_le_pureGradient hSob _
    _ = max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm u := by rw [freeEnergyState_pureGradientNorm]
    _ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * (Real.sqrt 3 * ‖u‖) :=
      mul_le_mul_of_nonneg_left (pureGradient_le_sqrt_three_energyState _)
        (le_trans (by norm_num) (le_max_right _ _))
    _ = _ := (mul_assoc _ _ _).symm

/-- Complex linearity and boundedness in the actual existing C43 norm. -/
def freeEnergyCLM (t : ℝ) : EnergyState →L[ℂ] EnergyState :=
  LinearMap.mkContinuous
    { toFun := freeEnergyState hDensity hSob t
      map_add' := freeEnergyState_add hDensity hSob t
      map_smul' := freeEnergyState_smul hDensity hSob t }
    (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3)
    (freeEnergyState_norm_bound hDensity hSob t)

theorem freeEnergyCLM_apply (t : ℝ) (u : EnergyState) :
    freeEnergyCLM hDensity hSob t u = freeEnergyState hDensity hSob t u := rfl

theorem freeEnergyState_continuous (t : ℝ) :
    Continuous (freeEnergyState hDensity hSob t) := (freeEnergyCLM hDensity hSob t).continuous

/-- Strong continuity of the constructed full orbit follows from the actual
L2 Fourier group on each gradient coordinate and the proved Sobolev topology. -/
theorem freeEnergyState_time_continuous (u : EnergyState) :
    Continuous (fun t : ℝ => freeEnergyState hDensity hSob t u) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_of_gradientTendsto hSob
  intro j
  simpa only [freeEnergyState_gradient] using
    (FreeFlow.freeL2_time_continuous (energyGradient j u)).tendsto a

/-- Distribution identity displaying the literal Fourier multiplier. -/
theorem freeEnergyState_fourier_distribution (t : ℝ) (u : EnergyState) :
    energyDistribution (freeEnergyState hDensity hSob t u) =
      TemperedDistribution.fourierMultiplierCLM ℂ
        (fun ξ : V => Complex.exp (-Complex.I * (t : ℂ) *
          ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 : ℝ))) (energyDistribution u) :=
  freeEnergyState_distribution hDensity hSob t u

end HartreeF.EnergySpace
