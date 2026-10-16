import FCriticalAffineIsometry
import FAffineMixedNormIdentity
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set LineDeriv
open scoped ENNReal Topology SchwartzMap RealInnerProductSpace
namespace HartreeF.CompactOrbitTerminal
open EnergySpace CriticalAffine
attribute [local irreducible] energySubmodule

abbrev gradientSourceExponent : ℝ≥0∞ := ENNReal.ofReal (6/5 : ℝ)
instance gradientSourceExponent_one_le : Fact (1 ≤ gradientSourceExponent) := ⟨by norm_num [gradientSourceExponent]⟩
abbrev GradientSource := Lp ℂ gradientSourceExponent (volume : Measure V)

local instance : ENNReal.HolderConjugate gradientSourceExponent 6 := by
  have h : Real.HolderTriple (6/5) 6 1 := by constructor <;> norm_num
  simpa only [gradientSourceExponent, ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h.ennrealOfReal

/-- Actual real L6/5-L6 spatial integral pairing. -/
def gradientSourcePair : GradientSource →L[ℝ] L6 →L[ℝ] ℝ :=
  (innerSL ℝ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).lpPairing volume gradientSourceExponent 6

theorem gradientSourcePair_bound (f : GradientSource) (g : L6) :
    ‖gradientSourcePair f g‖ ≤ ‖gradientSourcePair‖ * ‖f‖ * ‖g‖ :=
  gradientSourcePair.le_opNorm₂ f g

/-- Exact Jacobian and homogeneity on the actual pullback representative. -/
theorem gradientPullback_source_eLpNorm {a : ℝ} (ha : 0 < a) (b : V) (f : V → ℂ) :
    eLpNorm (gradientPullback a b f) gradientSourceExponent volume =
      ENNReal.ofReal a⁻¹ * eLpNorm f gradientSourceExponent volume := by
  have hs : a^(3/2 : ℝ) = a * Real.sqrt a := by
    calc
      a^(3/2 : ℝ) = a^((1 : ℝ)+(1/2 : ℝ)) := by congr 1; norm_num
      _ = a^(1 : ℝ) * a^(1/2 : ℝ) := Real.rpow_add ha _ _
      _ = a * Real.sqrt a := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h := AffineMixed.spatial_eLpNorm_affine ha b (3/2 : ℝ) gradientSourceExponent f
  have he : (3/2 : ℝ) - 3 * AffineMixed.reciprocalExponent gradientSourceExponent = -1 := by
    norm_num [AffineMixed.reciprocalExponent, gradientSourceExponent]
  rw [he, Real.rpow_neg_one, hs] at h
  exact h

def affineSchwartzGradientSource {a : ℝ} (ha : 0 < a) (b : V) (φ : Test) (j : Fin 3) :
    GradientSource :=
  (gradientPullback_memLp ha b
    (by norm_num [gradientSourceExponent]) (by simp [gradientSourceExponent])
    ((∂_{coordinate j} φ).memLp gradientSourceExponent volume)).toLp
      (gradientPullback a b ((∂_{coordinate j} φ : Test) : V → ℂ))

theorem affineSchwartzGradientSource_ae {a : ℝ} (ha : 0 < a) (b : V) (φ : Test) (j : Fin 3) :
    (affineSchwartzGradientSource ha b φ j : V → ℂ) =ᵐ[volume]
      gradientPullback a b ((∂_{coordinate j} φ : Test) : V → ℂ) :=
  MemLp.coeFn_toLp _

/-- The source representative is the SAME genuine coordinate weak gradient, not a
surrogate function with only a matching norm. -/
theorem affineSchwartzGradientSource_same_gradient {a : ℝ} (ha : 0 < a) (b : V)
    (φ : Test) (j : Fin 3) :
    (energyGradient j (affineState ha b (schwartzEnergyState φ)) : V → ℂ) =ᵐ[volume]
      affineSchwartzGradientSource ha b φ j := by
  have hp := (affine_quasiMeasurePreserving ha.ne' b).ae
    ((∂_{coordinate j} φ).coeFn_toLp 2 volume)
  filter_upwards [affineState_gradient_ae ha b (schwartzEnergyState φ) j,
    affineSchwartzGradientSource_ae ha b φ j, hp] with x hx hs hp
  rw [hx, hs]
  simp only [gradientPullback, schwartzEnergyState_gradient, hp]

theorem affineSchwartzGradientSource_norm {a : ℝ} (ha : 0 < a) (b : V)
    (φ : Test) (j : Fin 3) :
    ‖affineSchwartzGradientSource ha b φ j‖ =
      a⁻¹ * ‖(∂_{coordinate j} φ).toLp gradientSourceExponent volume‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (affineSchwartzGradientSource_ae ha b φ j),
    gradientPullback_source_eLpNorm ha b, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le), SchwartzMap.norm_toLp]

/-- Actual L2 weak pairing with a Schwartz test is the actual mixed-exponent
pairing of those SAME representatives. -/
theorem affineSchwartzGradient_inner_eq {a : ℝ} (ha : 0 < a) (b : V)
    (φ ψ : Test) (j : Fin 3) :
    inner ℝ (energyGradient j (affineState ha b (schwartzEnergyState φ)))
      (ψ.toLp 2 volume) =
      gradientSourcePair (affineSchwartzGradientSource ha b φ j) (ψ.toLp 6 volume) := by
  rw [L2.inner_def (𝕜 := ℝ), gradientSourcePair, ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [affineSchwartzGradientSource_same_gradient ha b φ j,
    ψ.coeFn_toLp 2 volume, ψ.coeFn_toLp 6 volume] with x hx h2 h6
  simp only [hx, h2, h6]
  rfl

/-- The physical length scale gains exactly r in L6/5, uniformly in its center. -/
theorem criticalAffineSchwartzGradient_inner_bound {r : ℝ} (hr : 0 < r) (y : V)
    (φ ψ : Test) (j : Fin 3) :
    ‖inner ℝ (energyGradient j (criticalAffineState r hr y (schwartzEnergyState φ)))
      (ψ.toLp 2 volume)‖ ≤
      ‖gradientSourcePair‖ * (r * ‖(∂_{coordinate j} φ).toLp gradientSourceExponent volume‖) * ‖ψ.toLp 6 volume‖ := by
  change ‖inner ℝ (energyGradient j (affineState (inv_pos.mpr hr) (-(r⁻¹ • y))
    (schwartzEnergyState φ))) (ψ.toLp 2 volume)‖ ≤ _
  rw [affineSchwartzGradient_inner_eq]
  simpa only [affineSchwartzGradientSource_norm, inv_inv] using
    gradientSourcePair_bound
      (affineSchwartzGradientSource (inv_pos.mpr hr) (-(r⁻¹ • y)) φ j) (ψ.toLp 6 volume)

end HartreeF.CompactOrbitTerminal
