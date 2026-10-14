import FActualCutoffLpOperators

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter Set LineDeriv InnerProductSpace
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalChargeBridge
open EnergySpace EnergySpace.Highpass SobolevStretch WeakHartreeProduct

variable {χ : V → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)

def localizedValue : EnergyState →L[ℂ] L2 := (cutoffL6L2 hχ.continuous hc).comp energyValue

def localizedGradient (j : Fin 3) : EnergyState →L[ℂ] L2 :=
  (cutoffL2L2 hχ.continuous hc).comp (energyGradient j) +
    (cutoffL6L2 (coefficientDerivative_continuous hχ j)
      (coefficientDerivative_compact hc j)).comp energyValue

theorem localizedValue_ae (u : EnergyState) :
    (localizedValue hχ hc u : V → ℂ) =ᵐ[volume] fun x => χ x • energyValue u x :=
  cutoffL6L2_ae hχ.continuous hc (energyValue u)

theorem localizedGradient_ae (u : EnergyState) (j : Fin 3) :
    (localizedGradient hχ hc j u : V → ℂ) =ᵐ[volume]
      fun x => χ x • energyGradient j u x + coefficientDerivative χ j x • energyValue u x := by
  filter_upwards [Lp.coeFn_add (cutoffL2L2 hχ.continuous hc (energyGradient j u))
      (cutoffL6L2 (coefficientDerivative_continuous hχ j) (coefficientDerivative_compact hc j) (energyValue u)),
    cutoffL2L2_ae hχ.continuous hc (energyGradient j u),
    cutoffL6L2_ae (coefficientDerivative_continuous hχ j) (coefficientDerivative_compact hc j)
      (energyValue u)] with x ha hb hd
  change (cutoffL2L2 hχ.continuous hc (energyGradient j u) +
    cutoffL6L2 (coefficientDerivative_continuous hχ j) (coefficientDerivative_compact hc j)
      (energyValue u)) x = _
  rw [ha, Pi.add_apply, hb, hd]

theorem cutoff_directionalField (u : EnergyState) (j : Fin 3) (x : V) :
    directionalField
      (fun y => χ y • energyProjectedGradient Complex.reCLM u y +
        (energyValue u y).re • gradient χ y)
      (fun y => χ y • energyProjectedGradient Complex.imCLM u y +
        (energyValue u y).im • gradient χ y) (coordinate j) x =
      χ x • energyGradient j u x + coefficientDerivative χ j x • energyValue u x := by
  apply Complex.ext <;>
    simp [directionalField, inner_add_left, real_inner_smul_left,
      energyProjectedGradient_coordinate, inner_gradient_left, coefficientDerivative,
      Complex.real_smul, mul_comm]

theorem localizedValue_derivative (u : EnergyState) (j : Fin 3) :
    ∂_{coordinate j} (Lp.toTemperedDistribution (localizedValue hχ hc u)) =
      Lp.toTemperedDistribution (localizedGradient hχ hc j u) := by
  let d := (energyState_inDotH1 u).cutoff hχ hc
  let h2 := (energyState_inDotH1 u).cutoff_memLp_two hχ hc
  have he : localizedValue hχ hc u = h2.toLp _ := by
    apply Lp.ext
    exact (localizedValue_ae hχ hc u).trans h2.coeFn_toLp.symm
  rw [he, weak_gradient_tempered_derivative h2 d.real_gradient_L2 d.imag_gradient_L2
    d.real_weak d.imag_weak]
  congr 1
  apply Lp.ext
  filter_upwards [(directionalField_memLp d.real_gradient_L2 d.imag_gradient_L2
      (coordinate j)).coeFn_toLp, localizedGradient_ae hχ hc u j] with x hd hg
  rw [hd, hg]
  exact cutoff_directionalField u j x

/-- Actual spatial multiplication into the closed L2/weak-gradient H1 graph. -/
def localizedH1CLM : EnergyState →L[ℂ] H1State :=
  ((localizedValue hχ hc).prod (ContinuousLinearMap.pi (localizedGradient hχ hc))).codRestrict
    h1Submodule (fun u => (mem_h1Submodule _).mpr (localizedValue_derivative hχ hc u))

theorem localizedH1_same_value (u : EnergyState) :
    ((localizedH1CLM hχ hc u).val.1 : V → ℂ) =ᵐ[volume]
      fun x => χ x • energyValue u x := localizedValue_ae hχ hc u

theorem localizedH1_same_gradient (u : EnergyState) (j : Fin 3) :
    ((localizedH1CLM hχ hc u).val.2 j : V → ℂ) =ᵐ[volume]
      fun x => χ x • energyGradient j u x + coefficientDerivative χ j x • energyValue u x :=
  localizedGradient_ae hχ hc u j

theorem localizedH1_continuousOn {T : Type*} [TopologicalSpace T]
    {u : T → EnergyState} {S : Set T} (hu : ContinuousOn u S) :
    ContinuousOn (fun t => localizedH1CLM hχ hc (u t)) S :=
  (localizedH1CLM hχ hc).continuous.comp_continuousOn hu

/-- The same literal physical cutoff used by the accepted mass conservation consumer. -/
def physicalCutoffH1 {R : ℝ} (hR : 0 < R) : EnergyState →L[ℂ] H1State :=
  localizedH1CLM (LocalChargeRigidity.chargeCutoff_smooth R)
    (LocalChargeRigidity.chargeCutoff_compact hR)

end HartreeF.LocalChargeBridge
