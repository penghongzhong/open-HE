import ComplexWeakCutoff
import ClassicalWeakGradient
import DirectionalKineticPositive
import GaugeReality
import VariationalHartreeThreshold

/-!
Literal weak stationary Hartree equation and the external ordinary inhomogeneous
H1 density interface. The density interface is Hunter, PDE Chapter 3,
Theorem 3.24, printed p. 59 / PDF page 15, specialized to R3, k=1, p=2.
https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf
It applies universally to real L2 functions with actual L2 weak gradients.
No self-test identity, homogeneous density, or problem-specific test extension
is part of either interface.
-/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal Topology
namespace HartreeF.StationarySelfTest
open SobolevStretch ForcingDomain

/-- The actual distributional stationary equation, tested only against genuine
compactly supported C-infinity real functions. -/
structure WeakStationary (α c : ℝ) (u : Space → ℂ)
    (GRe GIm : Space → Space) : Prop where
  sobolev : InDotH1 u GRe GIm
  real_equation : ∀ φ : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ x, ⟪GRe x, gradient φ x⟫) = ∫ x, (forcing α c u x).re * φ x
  imag_equation : ∀ φ : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ x, ⟪GIm x, gradient φ x⟫) = ∫ x, (forcing α c u x).im * φ x

/-- Ordinary universal inhomogeneous H1 density. In Hunter Definition 3.1,
the coordinate weak derivatives correspond to C11's arbitrary-direction
identity. Finite-dimensional Euclidean L2 gradient convergence is equivalent
to convergence of the three coordinate weak derivatives. All approximating
gradients here are the literal classical Mathlib gradient. -/
structure OrdinaryH1Density : Prop where
  approximate : ∀ (v : Space → ℝ) (V : Space → Space),
    MemLp v 2 volume → MemLp V 2 volume → HasWeakGradient v V →
    ∃ φ : ℕ → Space → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n)) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - v x) 2 volume) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => gradient (φ n) x - V x) 2 volume)
        atTop (𝓝 0)

#print axioms WeakStationary
#print axioms OrdinaryH1Density
end HartreeF.StationarySelfTest
