import FRetardedEnergyBound
import Mathlib.Topology.ContinuousMap.Compact

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal
namespace HartreeF.Retarded
open FreeFlow EnergySpace SobolevStretch StationarySelfTest

variable {T : Type*} [TopologicalSpace T]
    (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))

/-- Actual retarded states composed with any continuous time parameter. -/
def retardedEnergyCurve (τ : C(T, ℝ)) : C(T, EnergyState) :=
  ⟨fun x => retardedEnergyState hDensity hSob h F G hFG (τ x),
    (retardedEnergyState_time_continuous hDensity hSob h F G hFG).comp τ.continuous⟩

/-- Actual forward states composed with any continuous time parameter. -/
def forwardEnergyCurve (a : ℝ) (τ : C(T, ℝ)) : C(T, EnergyState) :=
  ⟨fun x => forwardEnergyState hDensity hSob h a F G hFG (τ x),
    (forwardEnergyState_time_continuous hDensity hSob h F G hFG a).comp τ.continuous⟩

theorem retardedEnergyCurve_apply (τ : C(T, ℝ)) (x : T) :
    retardedEnergyCurve hDensity hSob h F G hFG τ x =
      retardedEnergyState hDensity hSob h F G hFG (τ x) := rfl

theorem forwardEnergyCurve_apply (a : ℝ) (τ : C(T, ℝ)) (x : T) :
    forwardEnergyCurve hDensity hSob h F G hFG a τ x =
      forwardEnergyState hDensity hSob h a F G hFG (τ x) := rfl

variable [CompactSpace T]

/-- Supremum in time of the genuine graph norm. The bound is independent of τ and T. -/
theorem retardedEnergyCurve_norm (τ : C(T, ℝ)) :
    ‖retardedEnergyCurve hDensity hSob h F G hFG τ‖ ≤
      energyEndpointConstant K C * ‖G‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (energyEndpointConstant_nonneg h) (norm_nonneg G))).mpr
  intro x
  exact retardedEnergyState_norm hDensity hSob h F G hFG (τ x)

theorem forwardEnergyCurve_norm (a : ℝ) (τ : C(T, ℝ)) :
    ‖forwardEnergyCurve hDensity hSob h F G hFG a τ‖ ≤
      energyEndpointConstant K C * ‖G‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (energyEndpointConstant_nonneg h) (norm_nonneg G))).mpr
  intro x
  exact forwardEnergyState_norm hDensity hSob h F G hFG a (τ x)

variable (F' : EndpointSource) (G' : Fin 3 → EndpointSource)
    (hFG' : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F' s)) = Lp.toTemperedDistribution (G' j s))

theorem retardedEnergyCurve_sub_norm (τ : C(T, ℝ)) :
    ‖retardedEnergyCurve hDensity hSob h F G hFG τ -
      retardedEnergyCurve hDensity hSob h F' G' hFG' τ‖ ≤
      energyEndpointConstant K C * ‖G - G'‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (energyEndpointConstant_nonneg h) (norm_nonneg (G-G')))).mpr
  intro x
  exact retardedEnergyState_sub_norm hDensity hSob h F G hFG F' G' hFG' (τ x)

theorem forwardEnergyCurve_sub_norm (a : ℝ) (τ : C(T, ℝ)) :
    ‖forwardEnergyCurve hDensity hSob h F G hFG a τ -
      forwardEnergyCurve hDensity hSob h F' G' hFG' a τ‖ ≤
      energyEndpointConstant K C * ‖G - G'‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (energyEndpointConstant_nonneg h) (norm_nonneg (G-G')))).mpr
  intro x
  exact forwardEnergyState_sub_norm hDensity hSob h F G hFG F' G' hFG' a (τ x)

end HartreeF.Retarded
