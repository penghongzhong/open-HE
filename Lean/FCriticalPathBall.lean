import FCriticalPathSpace
import FHalfContraction

/-! Closed E+W path caps with an actual initial value. This module proves only
the topological fixed-point consumer. The concrete Hartree map must separately
supply its self-map and contraction bounds. No PDE conclusion is assumed here. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped Topology NNReal
namespace HartreeF.CriticalPathBall
open EnergySpace CriticalPathSpace

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
variable (μ : Measure T)

/-- All three genuine Bochner gradient coordinates, with their Pi maximum norm. -/
def gradientCoordinates : CriticalPath μ →L[ℂ] (Fin 3 → CriticalGradient μ) :=
  (ContinuousLinearMap.snd ℂ _ _).comp (criticalPathSubmodule μ).subtypeL

omit [CompactSpace T] in
theorem gradientCoordinates_apply (u : CriticalPath μ) (j : Fin 3) :
    gradientCoordinates μ u j = criticalGradient μ j u := rfl

theorem path_norm_eq (u : CriticalPath μ) :
    ‖u‖ = max ‖energyPath μ u‖ ‖gradientCoordinates μ u‖ := rfl

/-- A closed subset of the already proved complete E+W graph. -/
def admissiblePaths (t₀ : T) (f : EnergyState) (B η : ℝ) : Set (CriticalPath μ) :=
  {u | energyPath μ u t₀ = f ∧ ‖energyPath μ u‖ ≤ B ∧
    ‖gradientCoordinates μ u‖ ≤ η}

theorem admissiblePaths_isClosed (t₀ : T) (f : EnergyState) (B η : ℝ) :
    IsClosed (admissiblePaths μ t₀ f B η) := by
  apply IsClosed.inter
  · exact isClosed_eq
      ((ContinuousMap.evalCLM ℂ t₀).continuous.comp (energyPath μ).continuous)
      continuous_const
  · have hE : Continuous (fun u : CriticalPath μ => ‖energyPath μ u‖) := by
      change Continuous (fun u : CriticalPath μ => dist (energyPath μ u) 0)
      exact (energyPath μ).continuous.dist continuous_const
    have hW : Continuous (fun u : CriticalPath μ => ‖gradientCoordinates μ u‖) :=
      continuous_norm.comp (gradientCoordinates μ).continuous
    exact (isClosed_le hE continuous_const).inter (isClosed_le hW continuous_const)

theorem admissiblePaths_isComplete (t₀ : T) (f : EnergyState) (B η : ℝ) :
    IsComplete (admissiblePaths μ t₀ f B η) :=
  (admissiblePaths_isClosed μ t₀ f B η).isComplete

theorem admissiblePaths_norm_le {t₀ : T} {f : EnergyState} {B η : ℝ}
    {u : CriticalPath μ} (hu : u ∈ admissiblePaths μ t₀ f B η) :
    ‖u‖ ≤ max B η := by
  rw [path_norm_eq]
  exact max_le_max hu.2.1 hu.2.2

theorem admissiblePaths_coordinate_le {t₀ : T} {f : EnergyState} {B η : ℝ}
    {u : CriticalPath μ} (hu : u ∈ admissiblePaths μ t₀ f B η) (j : Fin 3) :
    ‖criticalGradient μ j u‖ ≤ η :=
  (norm_le_pi_norm (gradientCoordinates μ u) j).trans hu.2.2

theorem admissiblePaths_mem_of_coordinates {t₀ : T} {f : EnergyState} {B η : ℝ}
    {u : CriticalPath μ} (hη : 0 ≤ η) (hinit : energyPath μ u t₀ = f)
    (hE : ‖energyPath μ u‖ ≤ B) (hW : ∀ j, ‖criticalGradient μ j u‖ ≤ η) :
    u ∈ admissiblePaths μ t₀ f B η := by
  exact ⟨hinit, hE, (pi_norm_le_iff_of_nonneg hη).mpr hW⟩

/-- Banach's theorem on the actual closed path subset. Both quantitative inputs
are deliberately exposed until the concrete Hartree estimates instantiate them. -/
theorem exists_unique_fixedPoint_of_bounds (t₀ : T) (f : EnergyState) (B η : ℝ)
    (Φ : CriticalPath μ → CriticalPath μ)
    (hne : (admissiblePaths μ t₀ f B η).Nonempty)
    (hself : Set.MapsTo Φ (admissiblePaths μ t₀ f B η) (admissiblePaths μ t₀ f B η))
    (hcontract : ∀ u ∈ admissiblePaths μ t₀ f B η,
      ∀ v ∈ admissiblePaths μ t₀ f B η,
        ‖Φ u - Φ v‖ ≤ (1 / 2 : ℝ) * ‖u - v‖) :
    ∃ u ∈ admissiblePaths μ t₀ f B η, Φ u = u ∧
      ∀ v ∈ admissiblePaths μ t₀ f B η, Φ v = v → v = u := by
  let S := admissiblePaths μ t₀ f B η
  let : CompleteSpace S := (admissiblePaths_isClosed μ t₀ f B η).completeSpace_coe
  let : Nonempty S := hne.to_subtype
  let g : S → S := hself.restrict Φ S S
  have hg : ContractingWith (1 / 2 : ℝ≥0) g :=
    half_contracting_restrict S Φ hself hcontract
  let u := hg.fixedPoint g
  refine ⟨u.val, u.property, ?_, ?_⟩
  · exact congrArg Subtype.val hg.fixedPoint_isFixedPt
  · intro v hv hfix
    have hv' : Function.IsFixedPt g ⟨v, hv⟩ := Subtype.ext hfix
    exact congrArg Subtype.val (hg.fixedPoint_unique hv')

end HartreeF.CriticalPathBall
