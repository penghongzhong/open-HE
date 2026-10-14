import FActualLocalizedHartreePairing
import FActualQuadraticChargeRule

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.LocalDualSource
open EnergySpace LocalChargeBridge
attribute [local irreducible] energySubmodule

/-- The literal sesquilinear spatial integral, as a bounded real bilinear map. -/
def spatialPair (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q] :
    Lp ℂ p (volume : Measure V) →L[ℝ] Lp ℂ q (volume : Measure V) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ).lpPairing (volume : Measure V) p q).bilinearComp
    (ContinuousLinearMap.id ℝ _) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL q volume)

theorem spatialPair_integrable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (f : Lp ℂ p (volume : Measure V))
    (g : Lp ℂ q (volume : Measure V)) :
    Integrable (fun x : V => f x * star (g x)) volume :=
  (Lp.memLp f).integrable_mul
    ((Lp.memLp g).continuousLinearMap_comp (Complex.conjCLE : ℂ →L[ℝ] ℂ))

theorem spatialPair_eq_integral {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (f : Lp ℂ p (volume : Measure V))
    (g : Lp ℂ q (volume : Measure V)) :
    spatialPair p q f g = ∫ x : V, f x * star (g x) := by
  rw [spatialPair, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(Complex.conjCLE : ℂ →L[ℝ] ℂ).coeFn_compLpL g] with x hx
  change f x * ((Complex.conjCLE : ℂ →L[ℝ] ℂ).compLpL q volume g) x = _
  rw [hx]
  rfl

/-- Precomposition by an actual cutoff map, also continuous in operator norm. -/
def precomposeDual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : EnergyState →L[ℝ] E) : (E →L[ℝ] ℂ) →L[ℝ] (EnergyState →L[ℝ] ℂ) :=
  (ContinuousLinearMap.compL ℝ EnergyState E ℂ).flip A

/-- Continuous real projection of i times an actual complex functional. -/
def imaginaryRotationDual : (EnergyState →L[ℝ] ℂ) →L[ℝ] (EnergyState →L[ℝ] ℝ) :=
  (Complex.reCLM.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)).postcomp EnergyState

theorem imaginaryRotationDual_apply (f : EnergyState →L[ℝ] ℂ) (w : EnergyState) :
    imaginaryRotationDual f w = (Complex.I * f w).re := rfl

end HartreeF.LocalDualSource
