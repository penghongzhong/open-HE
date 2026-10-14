import PhaseKinetic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Actual nonlocal Hartree pressure and phase comparison. This is the static
principal-form identity only; it does not assert a PDE virial identity. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace
namespace HartreeF
abbrev Space := EuclideanSpace ℝ (Fin 3)
def modulus (h : Space → ℂ) : Space → ℂ := fun x => (‖h x‖ : ℂ)
def density (h : Space → ℂ) (x : Space) : ℝ := ‖h x‖^2
def powerDensity (α : ℝ) (h : Space → ℂ) (x : Space) : ℝ := ‖h x‖^(3+α)
def rieszKernel (α c : ℝ) (z : Space) : ℝ := c*‖z‖^(α-3)
def potential (α c : ℝ) (h : Space → ℂ) (x : Space) : ℝ :=
  ∫ z, rieszKernel α c (x-z)*powerDensity α h z
def densityField (gradK : Space → Space) (h : Space → ℂ) (x : Space) : Space :=
  ∫ y, density h y • gradK (x-y)
def lapDensityField (lapK : Space → ℝ) (h : Space → ℂ) (x : Space) : ℝ :=
  ∫ y, lapK (x-y)*density h y
def chordField (gradK : Space → Space) (h : Space → ℂ) (x z : Space) : ℝ :=
  ⟪densityField gradK h x-densityField gradK h z, x-z⟫ / ‖x-z‖^2
def endpointPressure (α c : ℝ) (lapK : Space → ℝ) (h : Space → ℂ) : ℝ :=
  ∫ x, lapDensityField lapK h x * potential α c h x * powerDensity α h x
def chordPressure (α c : ℝ) (gradK : Space → Space) (h : Space → ℂ) : ℝ :=
  ∫ z : Space × Space, rieszKernel α c (z.1-z.2) * chordField gradK h z.1 z.2 *
    powerDensity α h z.1 * powerDensity α h z.2 ∂volume.prod volume
def hartreePressure (α c : ℝ) (lapK : Space → ℝ) (gradK : Space → Space)
    (h : Space → ℂ) : ℝ :=
  (2*(1+α)/(3+α))*endpointPressure α c lapK h +
    (2*(3-α)/(3+α))*chordPressure α c gradK h
def densityQ (biLapK : Space → ℝ) (h : Space → ℂ) : ℝ :=
  -(∫ z : Space × Space, biLapK (z.1-z.2)*density h z.1*density h z.2
    ∂volume.prod volume)
def hartreePrincipal (α c : ℝ) (biLapK lapK : Space → ℝ)
    (gradK : Space → Space) (H : Space → Space → Fin 3 → Fin 3 → ℝ)
    (h : Space → ℂ) (dh : Space → Fin 3 → ℂ) : ℝ :=
  Phase.principal volume (densityQ biLapK h - hartreePressure α c lapK gradK h)
    H (Phase.stress h dh)

@[simp] theorem norm_modulus (h : Space → ℂ) (x : Space) : ‖modulus h x‖ = ‖h x‖ := by
  simp [modulus]
@[simp] theorem density_modulus (h : Space → ℂ) : density (modulus h) = density h := by
  funext x; simp [density]
@[simp] theorem powerDensity_modulus (α : ℝ) (h : Space → ℂ) :
    powerDensity α (modulus h) = powerDensity α h := by
  funext x; simp [powerDensity]
@[simp] theorem potential_modulus (α c : ℝ) (h : Space → ℂ) :
    potential α c (modulus h) = potential α c h := by funext x; simp [potential]
@[simp] theorem densityField_modulus (gradK : Space → Space) (h : Space → ℂ) :
    densityField gradK (modulus h) = densityField gradK h := by funext x; simp [densityField]
@[simp] theorem lapDensityField_modulus (lapK : Space → ℝ) (h : Space → ℂ) :
    lapDensityField lapK (modulus h) = lapDensityField lapK h := by funext x; simp [lapDensityField]
@[simp] theorem chordField_modulus (gradK : Space → Space) (h : Space → ℂ) :
    chordField gradK (modulus h) = chordField gradK h := by funext x z; simp [chordField]
@[simp] theorem hartreePressure_modulus (α c : ℝ) (lapK : Space → ℝ)
    (gradK : Space → Space) (h : Space → ℂ) :
    hartreePressure α c lapK gradK (modulus h) = hartreePressure α c lapK gradK h := by
  simp [hartreePressure, endpointPressure, chordPressure]
@[simp] theorem densityQ_modulus (biLapK : Space → ℝ) (h : Space → ℂ) :
    densityQ biLapK (modulus h) = densityQ biLapK h := by simp [densityQ]

theorem modulus_stress (h : Space → ℂ) (dg : Space → Fin 3 → ℝ) :
    Phase.stress (modulus h) (fun x i => (dg x i : ℂ)) = Phase.modulusStress h dg := by
  funext x y i j
  simp [Phase.stress, Phase.modulusStress, Phase.tensor, Phase.current, modulus]

theorem hartree_phase_difference (α c : ℝ) (biLapK lapK : Space → ℝ)
    (gradK : Space → Space) (H : Space → Space → Fin 3 → Fin 3 → ℝ)
    (h : Space → ℂ) (dh : Space → Fin 3 → ℂ) (dg Λ : Space → Fin 3 → ℝ)
    (polar : Phase.PolarIdentity volume h dh dg Λ)
    (heven : ∀ x y, H y x = H x y)
    (hi : Integrable (Phase.contraction H (Phase.stress h dh)) (volume.prod volume))
    (hg : Integrable (Phase.contraction H (Phase.modulusStress h dg)) (volume.prod volume)) :
    hartreePrincipal α c biLapK lapK gradK H h dh -
      hartreePrincipal α c biLapK lapK gradK H (modulus h) (fun x i => (dg x i : ℂ)) =
      2 * ∫ z, Phase.phaseSquare H h Λ z ∂volume.prod volume := by
  unfold hartreePrincipal
  simp only [densityQ_modulus, hartreePressure_modulus, modulus_stress]
  exact Phase.phase_difference_eq H h dh dg Λ _ polar heven hi hg

theorem hartree_convex_phase_reduction (α c : ℝ) (biLapK lapK : Space → ℝ)
    (gradK : Space → Space) (H : Space → Space → Fin 3 → Fin 3 → ℝ)
    (h : Space → ℂ) (dh : Space → Fin 3 → ℂ) (dg Λ : Space → Fin 3 → ℝ)
    (polar : Phase.PolarIdentity volume h dh dg Λ)
    (heven : ∀ x y, H y x = H x y)
    (hpos : ∀ x y (v : Fin 3 → ℝ), 0 ≤ ∑ i, ∑ j, H x y i j * v i * v j)
    (hi : Integrable (Phase.contraction H (Phase.stress h dh)) (volume.prod volume))
    (hg : Integrable (Phase.contraction H (Phase.modulusStress h dg)) (volume.prod volume)) :
    hartreePrincipal α c biLapK lapK gradK H (modulus h) (fun x i => (dg x i : ℂ)) ≤
      hartreePrincipal α c biLapK lapK gradK H h dh := by
  unfold hartreePrincipal
  simp only [densityQ_modulus, hartreePressure_modulus, modulus_stress]
  exact Phase.convex_phase_reduction H h dh dg Λ _ polar heven hpos hi hg

#print axioms hartreePressure_modulus
#print axioms modulus_stress
#print axioms hartree_phase_difference
#print axioms hartree_convex_phase_reduction
end HartreeF
