import FRetardedTimeContinuity
import FRetardedEnergyState
import FEnergyFreeProperties

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.Retarded
open FreeFlow EnergySpace SobolevStretch StationarySelfTest

/-- The existing constructed energy state at each actual retarded time. -/
def retardedEnergyState (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (t : ℝ) : EnergyState :=
  restrictedEnergyState hDensity hSob h F G hFG (Set.Iio t) measurableSet_Iio t

/-- Forward state with the same literal (a,t] scalar integral and three gradients. -/
def forwardEnergyState (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C) (a : ℝ)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))
    (t : ℝ) : EnergyState :=
  restrictedEnergyState hDensity hSob h F G hFG (Set.Ioc a t) measurableSet_Ioc t

variable (hDensity : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (h : OrdinaryEndpointBound C)
    (F : EndpointSource) (G : Fin 3 → EndpointSource)
    (hFG : ∀ j : Fin 3, ∀ᵐ s ∂volume,
      ∂_{coordinate j} (Lp.toTemperedDistribution (F s)) = Lp.toTemperedDistribution (G j s))

theorem retardedEnergyState_gradient (t : ℝ) (j : Fin 3) :
    energyGradient j (retardedEnergyState hDensity hSob h F G hFG t) = retardedL2 h (G j) t := rfl

theorem forwardEnergyState_gradient (a t : ℝ) (j : Fin 3) :
    energyGradient j (forwardEnergyState hDensity hSob h a F G hFG t) = forwardL2 h a (G j) t := rfl

/-- The graph-norm continuity is derived from the three actual gradient integrals. -/
theorem retardedEnergyState_time_continuous :
    Continuous (retardedEnergyState hDensity hSob h F G hFG) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  apply tendsto_of_gradientTendsto hSob
  intro j
  exact (retardedL2_time_continuous h (G j)).tendsto a

theorem forwardEnergyState_time_continuous (a : ℝ) :
    Continuous (forwardEnergyState hDensity hSob h a F G hFG) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_of_gradientTendsto hSob
  intro j
  exact (forwardL2_time_continuous h a (G j)).tendsto t

theorem retardedEnergyState_scalar (t : ℝ) (φ : FreeFlow.Test) :
    energyDistribution (retardedEnergyState hDensity hSob h F G hFG t) φ =
      ∫ s in Set.Iio t, scalarIntegrand t F φ s :=
  restrictedEnergyState_scalar hDensity hSob h F G hFG _ _ _ _

theorem forwardEnergyState_scalar (a t : ℝ) (φ : FreeFlow.Test) :
    energyDistribution (forwardEnergyState hDensity hSob h a F G hFG t) φ =
      ∫ s in Set.Ioc a t, scalarIntegrand t F φ s :=
  restrictedEnergyState_scalar hDensity hSob h F G hFG _ _ _ _

theorem forwardEnergyState_eq_zero_of_le (a t : ℝ) (ht : t ≤ a) :
    forwardEnergyState hDensity hSob h a F G hFG t = 0 := by
  apply energyDistribution_injective
  ext φ
  rw [forwardEnergyState_scalar, Set.Ioc_eq_empty_of_le ht]
  simp

theorem forwardEnergyState_initial (a : ℝ) :
    forwardEnergyState hDensity hSob h a F G hFG a = 0 :=
  forwardEnergyState_eq_zero_of_le hDensity hSob h F G hFG a a le_rfl

end HartreeF.Retarded
