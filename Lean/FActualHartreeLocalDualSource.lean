import FActualSpatialDualPairing

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.LocalDualSource
open EnergySpace LocalChargeBridge ForcingDomain ForcingContinuity
local instance energyRealSpace : NormedSpace ℝ EnergyState := inferInstance
local instance energyDualComplexNorm : NormedAddCommGroup (EnergyState →L[ℝ] ℂ) := inferInstance
local instance energyDualRealNorm : NormedAddCommGroup (EnergyState →L[ℝ] ℝ) := inferInstance
local instance energyDualComplexSpace : NormedSpace ℝ (EnergyState →L[ℝ] ℂ) := inferInstance
local instance energyDualRealSpace : NormedSpace ℝ (EnergyState →L[ℝ] ℝ) := inferInstance

local instance source_ge_one : Fact (1 ≤ ENNReal.ofReal (6/5 : ℝ)) := ⟨by norm_num⟩
local instance source_holder : ENNReal.HolderConjugate (ENNReal.ofReal (6/5 : ℝ)) 6 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  rw [ENNReal.toReal_add (by simp) (by simp)]
  norm_num

variable {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)

/-- The actual chi*w spatial test in L6, with no L2 input. -/
def localizedTestL6 : EnergyState →L[ℝ] L6 :=
  ((cutoffL6L6 hχ.continuous hc).comp energyValue).restrictScalars ℝ

/-- Actual kinetic pairing against the weak gradient of chi*w. -/
def kineticDualCLM : EnergyState →L[ℝ] (EnergyState →L[ℝ] ℂ) :=
  ∑ j : Fin 3,
    (precomposeDual ((localizedGradient hχ hc j).restrictScalars ℝ)).comp
      ((spatialPair 2 2).comp ((energyGradient j).restrictScalars ℝ))

/-- A true L^(6/5)-source to bounded-dual map, using chi*w as the L6 test. -/
def sourceToDualCLM : Retarded.SourceSpace →L[ℝ] (EnergyState →L[ℝ] ℂ) :=
  (precomposeDual (localizedTestL6 hχ hc)).comp
    (spatialPair (ENNReal.ofReal (6/5 : ℝ)) 6)

/-- The nonlinear derivative candidate is constructed from the literal original Hartree map. -/
def actualPDEDual {α c : ℝ} (hH : OrdinaryHLS α c) (u : EnergyState) :
    EnergyState →L[ℝ] ℝ :=
  imaginaryRotationDual (-kineticDualCLM hχ hc u +
    sourceToDualCLM hχ hc (forcingLp hH (energyValue u)))

def kineticIntegrand (u w : EnergyState) (j : Fin 3) (x : V) : ℂ :=
  energyGradient j u x * star (χ x • energyGradient j w x +
    coefficientDerivative χ j x • energyValue w x)

def sourceIntegrand (α c : ℝ) (u w : EnergyState) (x : V) : ℂ :=
  forcing α c (energyValue u) x * star (χ x • energyValue w x)

/-- Literal spatial weak form with its original source and its exact product gradient. -/
def spatialWeakForm (α c : ℝ) (u w : EnergyState) : ℂ :=
  -(∑ j : Fin 3, ∫ x : V, kineticIntegrand (χ := χ) u w j x) +
    ∫ x : V, sourceIntegrand (χ := χ) α c u w x

include hχ hc

theorem kineticIntegrand_integrable (u w : EnergyState) (j : Fin 3) :
    Integrable (kineticIntegrand (χ := χ) u w j) volume := by
  apply (spatialPair_integrable (energyGradient j u) (localizedGradient hχ hc j w)).congr
  filter_upwards [localizedGradient_ae hχ hc w j] with x hx
  change _ = energyGradient j u x * star _
  rw [hx]

theorem sourceIntegrand_integrable {α c : ℝ} (hH : OrdinaryHLS α c) (u w : EnergyState) :
    Integrable (sourceIntegrand (χ := χ) α c u w) volume := by
  apply (spatialPair_integrable (forcingLp hH (energyValue u))
    (cutoffL6L6 hχ.continuous hc (energyValue w))).congr
  filter_upwards [(forcing_memLp hH (Lp.memLp (energyValue u))).coeFn_toLp,
    cutoffL6L6_ae hχ.continuous hc (energyValue w)] with x hf hw
  change forcingLp hH (energyValue u) x * star (cutoffL6L6 hχ.continuous hc (energyValue w) x) = _
  rw [show forcingLp hH (energyValue u) x = _ from hf, hw]
  rfl

theorem kineticDualCLM_eq_integral (u w : EnergyState) :
    kineticDualCLM hχ hc u w = ∑ j : Fin 3, ∫ x : V, kineticIntegrand (χ := χ) u w j x := by
  simp only [kineticDualCLM, sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro j _
  change spatialPair 2 2 (energyGradient j u) (localizedGradient hχ hc j w) = _
  rw [spatialPair_eq_integral]
  apply integral_congr_ae
  filter_upwards [localizedGradient_ae hχ hc w j] with x hx
  change _ = energyGradient j u x * star _
  rw [hx]

theorem sourceToDualCLM_eq_integral {α c : ℝ} (hH : OrdinaryHLS α c) (u w : EnergyState) :
    sourceToDualCLM hχ hc (forcingLp hH (energyValue u)) w =
      ∫ x : V, sourceIntegrand (χ := χ) α c u w x := by
  change spatialPair (ENNReal.ofReal (6/5 : ℝ)) 6 (forcingLp hH (energyValue u))
    (cutoffL6L6 hχ.continuous hc (energyValue w)) = _
  rw [spatialPair_eq_integral]
  apply integral_congr_ae
  filter_upwards [(forcing_memLp hH (Lp.memLp (energyValue u))).coeFn_toLp,
    cutoffL6L6_ae hχ.continuous hc (energyValue w)] with x hf hw
  rw [show forcingLp hH (energyValue u) x = _ from hf, hw]
  rfl

/-- Exact genuine spatial-integral formula for the constructed real bounded dual. -/
theorem actualPDEDual_apply {α c : ℝ} (hH : OrdinaryHLS α c) (u w : EnergyState) :
    actualPDEDual hχ hc hH u w = (Complex.I * spatialWeakForm (χ := χ) α c u w).re := by
  change (Complex.I * (-(kineticDualCLM hχ hc u w) +
    sourceToDualCLM hχ hc (forcingLp hH (energyValue u)) w)).re = _
  rw [kineticDualCLM_eq_integral hχ hc, sourceToDualCLM_eq_integral hχ hc hH]
  rfl

/-- Strong continuity in the norm of the continuous dual, not merely tested scalar continuity. -/
theorem actualPDEDual_continuous {α c : ℝ} (hH : OrdinaryHLS α c) :
    Continuous (actualPDEDual hχ hc hH) :=
  imaginaryRotationDual.continuous.comp ((kineticDualCLM hχ hc).continuous.neg.add
    ((sourceToDualCLM hχ hc).continuous.comp ((forcingLp_continuous hH).comp energyValue.continuous)))

/-- A finite quantitative dual norm budget from actual operator norms and actual source norms. -/
theorem actualPDEDual_norm {α c : ℝ} (hH : OrdinaryHLS α c) (u : EnergyState) :
    ‖actualPDEDual hχ hc hH u‖ ≤ ‖imaginaryRotationDual‖ *
      (‖kineticDualCLM hχ hc‖ * ‖u‖ + ‖sourceToDualCLM hχ hc‖ * ‖forcingLp hH (energyValue u)‖) := by
  apply (imaginaryRotationDual.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hk : ‖-(kineticDualCLM hχ hc u)‖ ≤ ‖kineticDualCLM hχ hc‖ * ‖u‖ := by
    simpa only [norm_neg] using (kineticDualCLM hχ hc).le_opNorm u
  exact (norm_add_le _ _).trans (add_le_add hk ((sourceToDualCLM hχ hc).le_opNorm _))

/-- Valid on any exact time domain; it does not assert a weak or strong time derivative. -/
theorem actualPDEDual_continuousOn {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {S : Set ℝ} (hu : ContinuousOn u S) :
    ContinuousOn (fun t => actualPDEDual hχ hc hH (u t)) S :=
  (actualPDEDual_continuous hχ hc hH).comp_continuousOn hu

theorem actualPDEDual_time_integrable {α c : ℝ} (hH : OrdinaryHLS α c)
    {u : ℝ → EnergyState} {a b : ℝ} (hu : ContinuousOn u (Icc a b)) :
    IntegrableOn (fun t => actualPDEDual hχ hc hH (u t)) (Icc a b) volume :=
  (actualPDEDual_continuousOn hχ hc hH hu).integrableOn_Icc

end HartreeF.LocalDualSource
