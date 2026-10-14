import FBackwardFixedPointData
import FEndpointProjectedGradient

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped ENNReal
namespace HartreeF.ActualBackwardLocalFixedPoint
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain EndpointOutput
attribute [local irreducible] backwardHartreeDuhamelMap criticalPathIntervalSource
  energySubmodule criticalPathSubmodule energyPath energyDistribution
  freeCriticalPath intervalRetardedCriticalPath freeCriticalPath_endpointWitness
  intervalRetardedCriticalPath_endpointWitness

/-- Subtraction of actual endpoint coordinates preserves agreement with the
same difference of genuine energy derivatives. -/
def subtractEndpointWitnesses {T : Type*} [MeasurableSpace T] {μ : Measure T}
    {g h : T → EnergyState} (Wg : EndpointGradientWitness μ g)
    (Wh : EndpointGradientWitness μ h) : EndpointGradientWitness μ (fun t => g t - h t) where
  field j := Wg.field j - Wh.field j
  agrees j := by
    filter_upwards [Wg.agrees j, Wh.agrees j, Lp.coeFn_sub (Wg.field j) (Wh.field j)]
      with t hgt hht hsub
    rw [hsub, Pi.sub_apply, map_sub]
    filter_upwards [hgt, hht, Lp.coeFn_sub (Wg.field j t) (Wh.field j t),
      Lp.coeFn_sub (energyGradient j (g t)) (energyGradient j (h t))] with x hgx hhx hd hx
    simp only [Pi.sub_apply] at hd hx
    rw [hd, hx, hgx, hhx]

/-- The same advanced path receives its endpoint gradient from the full-source
free witness minus the already constructed retarded witness. -/
def intervalAdvancedCriticalPath_endpointWitness (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (F : CompatibleIntervalSource a b) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F)) := by
  let Wfull := freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
    (intervalTotalSourceEnergy hDensity hSob h0 F)
  let Wpast := intervalRetardedCriticalPath_endpointWitness hDensity hSob h0 hret heret F
  let W := subtractEndpointWitnesses Wfull Wpast
  refine ⟨W.field, ?_⟩
  intro j
  filter_upwards [W.agrees j] with t ht
  have he : energyPath _ (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret F) t =
      energyPath _ (freeCriticalPath hDensity hSob hfree a b (intervalTotalSourceEnergy hDensity hSob h0 F)) t -
      energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 hret F) t := by
    unfold intervalAdvancedCriticalPath
    exact criticalPath_energy_sub_apply _ _ t
  exact ht.trans (Filter.Eventually.of_forall fun x =>
    congrArg (fun w : EnergyState => energyGradient j w x) he.symm)

attribute [local irreducible] intervalAdvancedCriticalPath intervalAdvancedCriticalPath_endpointWitness

/-- Full endpoint regularity of the actual backward nonlinear map. -/
def backwardHartreeDuhamelMap_endpointWitness (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c a b : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (hab : a ≤ b) (ub : EnergyState)
    (u : CriticalPath (intervalMeasure a b)) :
    EndpointGradientWitness (intervalMeasure a b)
      (energyPath _ (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u)) := by
  let Wfree := freeCriticalPath_endpointWitness hDensity hSob hfree hefree a b
    (freeEnergyState hDensity hSob (-b) ub)
  let Wfuture := intervalAdvancedCriticalPath_endpointWitness hDensity hSob h0 hfree hret
    hefree heret (criticalPathIntervalSource hDensity hSob hH hab u 0)
  let W := subtractEndpointWitnesses Wfree (Wfuture.smul Complex.I)
  refine ⟨W.field, ?_⟩
  intro j
  filter_upwards [W.agrees j] with t ht
  have he : energyPath _ (backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab ub u) t =
      energyPath _ (freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)) t -
      Complex.I • energyPath _ (intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
        (criticalPathIntervalSource hDensity hSob hH hab u 0)) t := by
    let f := freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-b) ub)
    let r := intervalAdvancedCriticalPath hDensity hSob h0 hfree hret
      (criticalPathIntervalSource hDensity hSob hH hab u 0)
    have hs := criticalPath_energy_sub_apply f (Complex.I • r) t
    have hi := criticalPath_energy_smul_apply Complex.I r t
    unfold backwardHartreeDuhamelMap
    exact hs.trans (congrArg (fun z : EnergyState => energyPath (intervalMeasure a b) f t - z) hi)
  exact ht.trans (Filter.Eventually.of_forall fun x =>
    congrArg (fun w : EnergyState => energyGradient j w x) he.symm)

/-- Every energy terminal datum admits a positive left interval, the same full
Z path, the exact terminal value, and the literal negative-i future formula.
No initial L2 norm, variance, smallness, self-map, or solution hypothesis occurs. -/
theorem exists_actual_backward_mild_fullZ (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha c) (b : ℝ) (ub : EnergyState) :
    ∃ a : ℝ, ∃ hab : a < b, ∃ u : CriticalPath (intervalMeasure a b),
      energyPath _ u ⟨b, hab.le, le_rfl⟩ = ub ∧ FullZPath u ∧
      (∀ t : Set.Icc a b, ∀ φ : FreeFlow.Test,
        energyDistribution (energyPath _ u t) φ =
          FreeFlow.free ((t : ℝ)-b) (energyDistribution ub) φ - Complex.I *
            ∫ s in Set.Ioc (t : ℝ) b, ∫ x,
              (freeTest ((t : ℝ)-s) φ) x •
                forcing alpha c (energyValue
                  (extendEnergyPath hab.le (energyPath _ u) s)) x) := by
  let w := chosenBackwardFixedPoint hDensity hSob h0 hfree hret hH b ub
  refine ⟨w.left, w.left_lt, w.curve, w.terminal, ?_, ?_⟩
  · exact (congrArg (fun v : CriticalPath (intervalMeasure w.left b) => FullZPath v) w.fixed).mp
      ⟨backwardHartreeDuhamelMap_endpointWitness hDensity hSob h0 hfree hret
        hefree heret hH w.left_lt.le ub w.curve⟩
  · intro t φ
    have h := backwardHartreeDuhamelMap_literal_formula hDensity hSob h0 hfree hret hH
      w.left_lt.le ub w.curve t φ
    exact (congrArg
      (fun v : CriticalPath (intervalMeasure w.left b) =>
        energyDistribution (energyPath _ v t) φ) w.fixed).symm.trans h

end HartreeF.ActualBackwardLocalFixedPoint
