import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.NormNum

/-! Actual homogeneous energy state for F. Values are complex L6 classes;
three coordinate weak gradients are complex L2 classes. Distributional
compatibility is a closed-kernel constraint of actual continuous linear maps.
No L2 value domain or nonlinear solution-theory assumption is imposed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory LineDeriv
open scoped ENNReal
namespace HartreeF.EnergySpace

abbrev V := EuclideanSpace ℝ (Fin 3)
abbrev L2 := Lp ℂ 2 (volume : Measure V)
abbrev L6 := Lp ℂ 6 (volume : Measure V)
abbrev TD := TemperedDistribution V ℂ
abbrev Test := SchwartzMap V ℂ
instance : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩
def coordinate (j : Fin 3) : V := EuclideanSpace.single j (1 : ℝ)

abbrev EnergyAmbient := L6 × (Fin 3 → L2)

def energyResidual (j : Fin 3) : EnergyAmbient →L[ℂ] TD :=
  (lineDerivOpCLM ℂ TD (coordinate j)).comp
    ((Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 6).comp
      (ContinuousLinearMap.fst ℂ L6 (Fin 3 → L2))) -
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2).comp
    ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ L6 (Fin 3 → L2)))

def energySubmodule : Submodule ℂ EnergyAmbient := ⨅ j : Fin 3, (energyResidual j).ker

abbrev EnergyState := energySubmodule

theorem mem_energySubmodule (z : EnergyAmbient) : z ∈ energySubmodule ↔
    ∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution z.1) =
      Lp.toTemperedDistribution (z.2 j) := by
  simp only [energySubmodule, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ j : Fin 3, ∂_{coordinate j} (Lp.toTemperedDistribution z.1) -
    Lp.toTemperedDistribution (z.2 j) = 0) ↔ _
  simp only [sub_eq_zero]

theorem energySubmodule_isClosed : IsClosed (energySubmodule : Set EnergyAmbient) := by
  have he : (energySubmodule : Set EnergyAmbient) = ⋂ j : Fin 3, {z | energyResidual j z = 0} := by
    ext z
    change z ∈ energySubmodule ↔ _
    simp only [energySubmodule, Submodule.mem_iInf, LinearMap.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [he]
  exact isClosed_iInter (fun j => isClosed_eq (energyResidual j).continuous continuous_const)

instance energyState_complete : CompleteSpace EnergyState := energySubmodule_isClosed.completeSpace_coe

theorem energyState_value_norm_le (u : EnergyState) : ‖u.val.1‖ ≤ ‖u‖ := le_max_left _ _

theorem energyState_gradient_norm_le (u : EnergyState) (j : Fin 3) : ‖u.val.2 j‖ ≤ ‖u‖ :=
  (norm_le_pi_norm u.val.2 j).trans (le_max_right _ _)

def energyValue : EnergyState →L[ℂ] L6 :=
  (ContinuousLinearMap.fst ℂ L6 (Fin 3 → L2)).comp energySubmodule.subtypeL

def energyGradient (j : Fin 3) : EnergyState →L[ℂ] L2 :=
  (ContinuousLinearMap.proj j).comp
    ((ContinuousLinearMap.snd ℂ L6 (Fin 3 → L2)).comp energySubmodule.subtypeL)

def energyDistribution : EnergyState →L[ℂ] TD :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 6).comp energyValue

def energyGradientDistribution (j : Fin 3) : EnergyState →L[ℂ] TD :=
  (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2).comp (energyGradient j)

theorem energyValue_apply (u : EnergyState) : energyValue u = u.val.1 := rfl

theorem energyGradient_apply (u : EnergyState) (j : Fin 3) :
    energyGradient j u = u.val.2 j := rfl

theorem energyDistribution_derivative (u : EnergyState) (j : Fin 3) :
    LineDeriv.lineDerivOp (coordinate j) (energyDistribution u) =
      energyGradientDistribution j u := (mem_energySubmodule u.val).mp u.property j

end HartreeF.EnergySpace
