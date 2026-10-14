import FRegularizedSourceRepresentatives
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HartreeF.Regularization.Actual
open EnergySpace EnergyRegularizer SobolevStretch StationarySelfTest
open CriticalPathSpace IntervalTimeTransport
attribute [local instance] sourceEnergyNormedSpace sourcePathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath

def regularizedGradientOnInterval (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (n : ℕ) (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    C(Set.Icc a b, L6) :=
  ⟨fun t => energyValue ((firstCutoff n j).energyCLM hDensity hSob (energyPath _ u t)),
    energyValue.continuous.comp (((firstCutoff n j).energyCLM hDensity hSob).continuous.comp
      (energyPath _ u).continuous)⟩

/-- Genuine L2_t L6_x coordinate of the actual regularized gradient, for
all finite n. Its constructor uses continuity and finite interval measure. -/
def regularizedGradientLp (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) : Lp L6 2 (localMeasure a b) :=
  toLocalLp hab 2 (ContinuousMap.toLp 2 (intervalMeasure a b) ℂ
    (regularizedGradientOnInterval hDensity hSob n u j))

theorem regularizedGradientLp_coeFn (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ∀ᵐ t ∂localMeasure a b, regularizedGradientLp hDensity hSob hab n u j t =
      energyValue ((firstCutoff n j).energyCLM hDensity hSob
        (extendEnergyPath hab (energyPath _ u) t)) := by
  let f := regularizedGradientOnInterval hDensity hSob n u j
  filter_upwards [toLocalLp_coeFn hab 2 (ContinuousMap.toLp 2 (intervalMeasure a b) ℂ f),
    ae_clamp hab (ContinuousMap.coeFn_toLp (p := 2) (intervalMeasure a b) (𝕜 := ℂ) f)]
    with t ht hf
  exact ht.trans hf

theorem regularizedGradientLp_agrees (hDensity : OrdinaryH1Density) {K a b : ℝ}
    (hSob : OrdinarySobolev K) (hab : a ≤ b) (n : ℕ)
    (u : CriticalPath (intervalMeasure a b)) (j : Fin 3) :
    ∀ᵐ t ∂localMeasure a b,
      (regularizedGradientLp hDensity hSob hab n u j t : V → ℂ) =ᵐ[volume]
      energyGradient j (J hDensity hSob n (extendEnergyPath hab (energyPath _ u) t)) := by
  filter_upwards [regularizedGradientLp_coeFn hDensity hSob hab n u j] with t ht
  rw [ht]
  exact firstCutoff_value_gradient_ae hDensity hSob n _ j

#print axioms regularizedGradientLp
#print axioms regularizedGradientLp_coeFn
#print axioms regularizedGradientLp_agrees
end HartreeF.Regularization.Actual
