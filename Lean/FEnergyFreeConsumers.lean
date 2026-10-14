import FEnergyFreeProperties

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.EnergySpace
open SobolevStretch StationarySelfTest
variable (hDensity : OrdinaryH1Density) {K : ℝ} (hSob : OrdinarySobolev K)

theorem freeEnergyState_inDotH1 (t : ℝ) (u : EnergyState) :
    InDotH1 (energyValue (freeEnergyState hDensity hSob t u))
      (energyProjectedGradient Complex.reCLM (freeEnergyState hDensity hSob t u))
      (energyProjectedGradient Complex.imCLM (freeEnergyState hDensity hSob t u)) :=
  energyState_inDotH1 _

include hDensity hSob in
/-- Existing genuine homogeneous weak-gradient data now has an actual full
free trajectory, without a value-L2 or finite-variance premise. -/
theorem inDotH1_free_orbit {f : Space → ℂ} {U W : Space → Space} (hf : InDotH1 f U W) :
    ∃ u : ℝ → EnergyState,
      u 0 = inDotEnergyState hf ∧ Continuous u ∧
      (∀ t j, energyGradient j (u t) =
        FreeFlow.freeL2 t (energyGradient j (inDotEnergyState hf))) ∧
      (∀ t, energyDistribution (u t) =
        FreeFlow.free t (energyDistribution (inDotEnergyState hf))) ∧
      (∀ t, pureGradientNorm (u t) = pureGradientNorm (inDotEnergyState hf)) := by
  refine ⟨fun t => freeEnergyState hDensity hSob t (inDotEnergyState hf),
    freeEnergyState_zero_time hDensity hSob _, freeEnergyState_time_continuous hDensity hSob _,
    ?_, ?_, ?_⟩
  · exact fun t j => freeEnergyState_gradient hDensity hSob t _ j
  · exact fun t => freeEnergyState_distribution hDensity hSob t _
  · exact fun t => freeEnergyState_pureGradientNorm hDensity hSob t _

theorem freeEnergyState_sub (t : ℝ) (u v : EnergyState) :
    freeEnergyState hDensity hSob t (u - v) =
      freeEnergyState hDensity hSob t u - freeEnergyState hDensity hSob t v :=
  (freeEnergyCLM hDensity hSob t).map_sub u v

theorem freeEnergyState_difference_pureGradient (t : ℝ) (u v : EnergyState) :
    pureGradientNorm (freeEnergyState hDensity hSob t u - freeEnergyState hDensity hSob t v) =
      pureGradientNorm (u - v) := by
  rw [← freeEnergyState_sub, freeEnergyState_pureGradientNorm]

theorem freeEnergyState_left_inverse (t : ℝ) (u : EnergyState) :
    freeEnergyState hDensity hSob (-t) (freeEnergyState hDensity hSob t u) = u := by
  simpa only [neg_neg] using freeEnergyState_inverse hDensity hSob (-t) u

theorem freeEnergyState_bijective (t : ℝ) :
    Function.Bijective (freeEnergyState hDensity hSob t) :=
  ⟨Function.LeftInverse.injective (freeEnergyState_left_inverse hDensity hSob t),
    Function.RightInverse.surjective (freeEnergyState_inverse hDensity hSob t)⟩

theorem freeEnergyCLM_group (s t : ℝ) :
    freeEnergyCLM hDensity hSob (s + t) =
      (freeEnergyCLM hDensity hSob s).comp (freeEnergyCLM hDensity hSob t) := by
  apply ContinuousLinearMap.ext
  intro u
  exact freeEnergyState_add_time hDensity hSob s t u

/-- Only the quadratic kinetic term is preserved here. No Hartree interaction
term or total nonlinear energy preservation is asserted. -/
theorem freeEnergyState_kinetic (t : ℝ) (u : EnergyState) :
    kinetic (energyProjectedGradient Complex.reCLM (freeEnergyState hDensity hSob t u))
      (energyProjectedGradient Complex.imCLM (freeEnergyState hDensity hSob t u)) =
    kinetic (energyProjectedGradient Complex.reCLM u) (energyProjectedGradient Complex.imCLM u) := by
  rw [state_kinetic_eq_gradientSquared, state_kinetic_eq_gradientSquared,
    freeEnergyState_gradientSquared]

end HartreeF.EnergySpace
