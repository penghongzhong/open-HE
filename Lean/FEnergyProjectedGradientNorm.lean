import FEnergyGradientNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
All fields below are the canonical projected
gradients of the same original EnergyState.  No L2 hypothesis is placed on its
value, and no independent or existential gradient fields are introduced.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HartreeF.EnergySpace
open SobolevStretch

/-- Coordinatewise contraction followed by the finite-sum L2 triangle inequality.
The right side consists of the actual L2 coordinate gradients of `u`. -/
theorem energyProjectedGradient_eLpNorm_two_le_coordinate_sum
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) (u : EnergyState) :
    eLpNorm (energyProjectedGradient L u) 2 volume ≤
      ∑ j : Fin 3, eLpNorm (energyGradient j u) 2 volume := by
  calc
    _ ≤ ∑ j : Fin 3,
        eLpNorm (fun x => L (energyGradient j u x) • coordinate j) 2 volume := by
      change eLpNorm
        (fun x => ∑ j : Fin 3, L (energyGradient j u x) • coordinate j) 2 volume ≤ _
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (μ := (volume : Measure V))
          (f := fun j : Fin 3 => fun x => L (energyGradient j u x) • coordinate j)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
      apply eLpNorm_mono
        ((L.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).smul_const
          (coordinate j))
      intro x
      simpa [norm_smul, coordinate] using hL (energyGradient j u x)

/-- A deliberately nonoptimal constant 3 avoids any auxiliary value-space norm. -/
theorem energyProjectedGradient_norm_two_le_three_pureGradient
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖) (u : EnergyState) :
    (eLpNorm (energyProjectedGradient L u) 2 volume).toReal ≤
      3 * pureGradientNorm u := by
  have hfin : ∀ j : Fin 3, eLpNorm (energyGradient j u) 2 volume ≠ ∞ :=
    fun j => (Lp.memLp (energyGradient j u)).eLpNorm_ne_top
  calc
    _ ≤ (∑ j : Fin 3, eLpNorm (energyGradient j u) 2 volume).toReal :=
      ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun j _ => hfin j))
        (energyProjectedGradient_eLpNorm_two_le_coordinate_sum L hL u)
    _ = ∑ j : Fin 3, ‖energyGradient j u‖ := by
      rw [ENNReal.toReal_sum (fun j _ => hfin j)]
      simp only [← Lp.norm_def]
    _ ≤ ∑ _j : Fin 3, pureGradientNorm u :=
      Finset.sum_le_sum (fun j _ => energyGradient_le_pureGradient u j)
    _ = 3 * pureGradientNorm u := by simp

/-- The operator-norm formulation of the same actual projected-gradient bound. -/
theorem energyProjectedGradient_norm_two_le_three_pureGradient_of_norm_le_one
    (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (u : EnergyState) :
    (eLpNorm (energyProjectedGradient L u) 2 volume).toReal ≤
      3 * pureGradientNorm u := by
  apply energyProjectedGradient_norm_two_le_three_pureGradient L _ u
  intro z
  calc
    ‖L z‖ ≤ ‖L‖ * ‖z‖ := L.le_opNorm z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg z)
    _ = ‖z‖ := one_mul _

/-- The real scalar majorant used in the Hartree product estimate is genuinely L2.
Both summands use the canonical projections of this one state. -/
theorem energyProjectedGradient_norm_sum_memLp (u : EnergyState) :
    MemLp (fun x => ‖energyProjectedGradient Complex.reCLM u x‖ +
      ‖energyProjectedGradient Complex.imCLM u x‖) 2 volume :=
  (energyProjectedGradient_memLp Complex.reCLM u).norm.add
    (energyProjectedGradient_memLp Complex.imCLM u).norm

/-- Actual canonical Re/Im gradient majorant bounded solely by the pure-gradient
norm of the original state.  The explicit constant 6 is nonoptimal. -/
theorem energyProjectedGradient_norm_sum_le_six_pureGradient (u : EnergyState) :
    (eLpNorm (fun x => ‖energyProjectedGradient Complex.reCLM u x‖ +
      ‖energyProjectedGradient Complex.imCLM u x‖) 2 volume).toReal ≤
      6 * pureGradientNorm u := by
  have hR := energyProjectedGradient_memLp Complex.reCLM u
  have hI := energyProjectedGradient_memLp Complex.imCLM u
  have hRfin := hR.norm.eLpNorm_ne_top
  have hIfin := hI.norm.eLpNorm_ne_top
  calc
    _ ≤ (eLpNorm (fun x => ‖energyProjectedGradient Complex.reCLM u x‖) 2 volume +
        eLpNorm (fun x => ‖energyProjectedGradient Complex.imCLM u x‖) 2 volume).toReal := by
      apply ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hRfin, hIfin⟩)
      exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ = (eLpNorm (energyProjectedGradient Complex.reCLM u) 2 volume).toReal +
        (eLpNorm (energyProjectedGradient Complex.imCLM u) 2 volume).toReal := by
      rw [ENNReal.toReal_add hRfin hIfin,
        eLpNorm_norm _ hR.aestronglyMeasurable,
        eLpNorm_norm _ hI.aestronglyMeasurable]
    _ ≤ 3 * pureGradientNorm u + 3 * pureGradientNorm u :=
      add_le_add
        (energyProjectedGradient_norm_two_le_three_pureGradient
          Complex.reCLM Complex.abs_re_le_norm u)
        (energyProjectedGradient_norm_two_le_three_pureGradient
          Complex.imCLM Complex.abs_im_le_norm u)
    _ = 6 * pureGradientNorm u := by ring

end HartreeF.EnergySpace
