import FHartreeEnergyFrechet
import FEnergyGradientNorm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual Hartree total energy on the canonical homogeneous EnergyState.
The curve derivative requires its explicit strong EnergyState derivative;
it does not assert time differentiability or conservation of a mild solution. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace Topology
namespace HartreeF.StateEnergy
open EnergySpace EnergyVariation ForcingDomain

attribute [local irreducible] energySubmodule

def totalEnergy (α : ℝ) (u : EnergyState) : ℝ :=
  gradientSquared u / 2 - interactionLp α (energyValue u) / (2 * (3 + α))

theorem gradientSquared_contDiff : ContDiff ℝ 1 gradientSquared := by
  unfold gradientSquared
  exact ContDiff.sum (fun j _ =>
    ((energyGradient j).restrictScalars ℝ).contDiff.norm_sq ℂ)

theorem totalEnergy_contDiff {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α)) :
    ContDiff ℝ 1 (totalEnergy α) := by
  exact (gradientSquared_contDiff.div_const 2).sub
    (((interactionLp_contDiff_one hH).comp
      (energyValue.restrictScalars ℝ).contDiff).div_const _)

theorem gradientSquared_curve_hasDerivAt
    {u : ℝ → EnergyState} {du : EnergyState} {t : ℝ}
    (hu : HasDerivAt u du t) :
    HasDerivAt (fun s => gradientSquared (u s))
      (2 * ∑ j : Fin 3, inner ℝ (energyGradient j (u t)) (energyGradient j du)) t := by
  have hg (j : Fin 3) : HasDerivAt (fun s => energyGradient j (u s))
      (energyGradient j du) t :=
    ((energyGradient j).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hg j).norm_sq)
  simpa only [gradientSquared, Finset.mul_sum] using hs

theorem totalEnergy_curve_hasDerivAt {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {u : ℝ → EnergyState} {du : EnergyState} {t : ℝ}
    (hu : HasDerivAt u du t) :
    HasDerivAt (fun s => totalEnergy α (u s))
      ((∑ j : Fin 3, inner ℝ (energyGradient j (u t)) (energyGradient j du)) -
        (∫ x, star (forcing α (HeatRiesz.standardRieszConstant α)
          (energyValue (u t)) x) * energyValue du x).re) t := by
  have hv : HasDerivAt (fun s => energyValue (u s)) (energyValue du) t :=
    (energyValue.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu
  have hk : HasDerivAt (fun s => gradientSquared (u s) / 2)
      (∑ j : Fin 3, inner ℝ (energyGradient j (u t)) (energyGradient j du)) t := by
    convert! (gradientSquared_curve_hasDerivAt hu).div_const 2 using 1
    ring
  have hp := normalizedInteractionLp_curve_hasDerivAt hH hv
  exact hk.sub hp

/-- The exact paper kinetic integral, including both real and imaginary parts. -/
theorem totalEnergy_eq_literal (α : ℝ) (u : EnergyState) :
    totalEnergy α u =
      SobolevStretch.kinetic (energyProjectedGradient Complex.reCLM u)
        (energyProjectedGradient Complex.imCLM u) / 2 -
      DirectionalCoercivity.interaction α (energyValue u) / (2 * (3 + α)) := by
  rw [state_kinetic_eq_gradientSquared]
  rfl

theorem totalEnergy_tendsto {α : ℝ}
    (hH : OrdinaryHLS α (HeatRiesz.standardRieszConstant α))
    {ι : Type*} {l : Filter ι} {u : ι → EnergyState} {v : EnergyState}
    (hu : Tendsto u l (𝓝 v)) : Tendsto (fun n => totalEnergy α (u n)) l
      (𝓝 (totalEnergy α v)) :=
  (totalEnergy_contDiff hH).continuous.continuousAt.tendsto.comp hu

#print axioms totalEnergy
#print axioms gradientSquared_contDiff
#print axioms totalEnergy_contDiff
#print axioms gradientSquared_curve_hasDerivAt
#print axioms totalEnergy_curve_hasDerivAt
#print axioms totalEnergy_eq_literal
#print axioms totalEnergy_tendsto
end HartreeF.StateEnergy
