import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Independent F adaptation of D Lemma 2.1. The local sextic pressure
has been removed from both stresses: Hartree pressure is a nonlocal density-only
functional and is handled explicitly in HartreePhase. No D olean is imported.
The only analytic input here is the explicit Sobolev polar identity. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators

namespace HartreeF.Phase

variable {X : Type*} [MeasurableSpace X] {n : Type*} [Fintype n]
variable {μ : Measure X}

def current (h : X → ℂ) (dh : X → n → ℂ) (x : X) (i : n) : ℝ :=
  (star (h x) * dh x i).im

def tensor (dh : X → n → ℂ) (x : X) (i j : n) : ℝ :=
  (star (dh x i) * dh x j).re

def PolarIdentity (μ : Measure X) (h : X → ℂ) (dh : X → n → ℂ)
    (dg Λ : X → n → ℝ) : Prop :=
  ∀ᵐ x ∂μ, (∀ i, current h dh x i = ‖h x‖ * Λ x i) ∧
    (∀ i j, tensor dh x i j = dg x i * dg x j + Λ x i * Λ x j)

def stress (h : X → ℂ) (dh : X → n → ℂ) (x y : X) (i j : n) : ℝ :=
  ‖h y‖ ^ 2 * tensor dh x i j - current h dh y i * current h dh x j

def modulusStress (h : X → ℂ) (dg : X → n → ℝ) (x y : X) (i j : n) : ℝ :=
  ‖h y‖ ^ 2 * (dg x i * dg x j)

def contraction (H : X → X → n → n → ℝ)
    (S : X → X → n → n → ℝ) (z : X × X) : ℝ :=
  ∑ i, ∑ j, H z.1 z.2 i j * S z.1 z.2 i j

def phaseVector (h : X → ℂ) (Λ : X → n → ℝ) (x y : X) (i : n) : ℝ :=
  ‖h y‖ * Λ x i - ‖h x‖ * Λ y i

def phaseSquare (H : X → X → n → n → ℝ) (h : X → ℂ)
    (Λ : X → n → ℝ) (z : X × X) : ℝ :=
  ∑ i, ∑ j, H z.1 z.2 i j * phaseVector h Λ z.1 z.2 i *
    phaseVector h Λ z.1 z.2 j

def principal (μ : Measure X) (Q : ℝ) (H : X → X → n → n → ℝ)
    (S : X → X → n → n → ℝ) : ℝ :=
  Q + 4 * ∫ z, contraction H S z ∂μ.prod μ

theorem symmetrized_entry (a b xi xj yi yj gi gj hi hj c d : ℝ) :
    (b ^ 2 * (gi * gj + xi * xj) - (b * yi) * (a * xj) - c -
      (b ^ 2 * (gi * gj) - c)) +
    (a ^ 2 * (hi * hj + yi * yj) - (a * xi) * (b * yj) - d -
      (a ^ 2 * (hi * hj) - d)) =
    (b * xi - a * yi) * (b * xj - a * yj) := by ring

omit [MeasurableSpace X] in
theorem pointwise_identity
    (H : X → X → n → n → ℝ) (h : X → ℂ) (dh : X → n → ℂ)
    (dg Λ : X → n → ℝ) (x y : X)
    (hH : H y x = H x y)
    (hx : (∀ i, current h dh x i = ‖h x‖ * Λ x i) ∧
      (∀ i j, tensor dh x i j = dg x i * dg x j + Λ x i * Λ x j))
    (hy : (∀ i, current h dh y i = ‖h y‖ * Λ y i) ∧
      (∀ i j, tensor dh y i j = dg y i * dg y j + Λ y i * Λ y j)) :
    (contraction H (stress h dh) (x,y) - contraction H (modulusStress h dg) (x,y)) +
    (contraction H (stress h dh) (y,x) - contraction H (modulusStress h dg) (y,x)) =
    phaseSquare H h Λ (x,y) := by
  simp only [contraction, phaseSquare, hH, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [stress, modulusStress, phaseVector, hx.1, hy.1, hx.2, hy.2]
  ring

/-- The exact identity B_k[h]-B_k[|h|] = 2 integral of the phase square. -/
theorem phase_difference_eq [SFinite (μ : Measure X)]
    (H : X → X → n → n → ℝ) (h : X → ℂ) (dh : X → n → ℂ)
    (dg Λ : X → n → ℝ) (Q : ℝ)
    (polar : PolarIdentity μ h dh dg Λ)
    (heven : ∀ x y, H y x = H x y)
    (hi : Integrable (contraction H (stress h dh)) (μ.prod μ))
    (hg : Integrable (contraction H (modulusStress h dg)) (μ.prod μ)) :
    principal μ Q H (stress h dh) - principal μ Q H (modulusStress h dg) =
      2 * ∫ z, phaseSquare H h Λ z ∂μ.prod μ := by
  let D := fun z : X × X =>
    contraction H (stress h dh) z - contraction H (modulusStress h dg) z
  have hD : Integrable D (μ.prod μ) := hi.sub hg
  have hswap : (∫ z, D z.swap ∂μ.prod μ) = ∫ z, D z ∂μ.prod μ :=
    integral_prod_swap D
  have hid : (fun z => D z + D z.swap) =ᵐ[μ.prod μ] phaseSquare H h Λ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae polar,
      Measure.quasiMeasurePreserving_snd.tendsto_ae polar] with z hx hy
    exact pointwise_identity H h dh dg Λ z.1 z.2 (heven z.1 z.2) hx hy
  have hint := integral_congr_ae hid
  have hDs : Integrable (fun z => D z.swap) (μ.prod μ) := hD.swap
  rw [integral_add hD hDs, hswap] at hint
  have hdiff : (∫ z, D z ∂μ.prod μ) =
      (∫ z, contraction H (stress h dh) z ∂μ.prod μ) -
      (∫ z, contraction H (modulusStress h dg) z ∂μ.prod μ) :=
    integral_sub hi hg
  dsimp [principal]
  linarith

/-- Lemma 2.1, relative only to the registered Sobolev polar interface. -/
theorem convex_phase_reduction [SFinite (μ : Measure X)]
    (H : X → X → n → n → ℝ) (h : X → ℂ) (dh : X → n → ℂ)
    (dg Λ : X → n → ℝ) (Q : ℝ)
    (polar : PolarIdentity μ h dh dg Λ)
    (heven : ∀ x y, H y x = H x y)
    (hpos : ∀ x y (v : n → ℝ), 0 ≤ ∑ i, ∑ j, H x y i j * v i * v j)
    (hi : Integrable (contraction H (stress h dh)) (μ.prod μ))
    (hg : Integrable (contraction H (modulusStress h dg)) (μ.prod μ)) :
    principal μ Q H (modulusStress h dg) ≤ principal μ Q H (stress h dh) := by
  have hp : 0 ≤ ∫ z, phaseSquare H h Λ z ∂μ.prod μ :=
    integral_nonneg fun z => hpos z.1 z.2 (phaseVector h Λ z.1 z.2)
  have hid := phase_difference_eq H h dh dg Λ Q polar heven hi hg
  linarith

#print axioms symmetrized_entry
#print axioms pointwise_identity
#print axioms phase_difference_eq
#print axioms convex_phase_reduction

end HartreeF.Phase
