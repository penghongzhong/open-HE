import FCompactDenseUniformZero
import FAffineSchwartzGradientPair
import FFreeSchwartzL6Decay
import FWeakGradientEnergyDual

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal Topology SchwartzMap RealInnerProductSpace
namespace HartreeF.CompactOrbitTerminal
open EnergySpace CriticalAffine SobolevStretch StationarySelfTest ActualStrichartz
attribute [local irreducible] energySubmodule

/-- Real Hilbert adjoint of the very same native free Fourier group. -/
theorem actual_freeL2_real_adjoint (t : ℝ) (u v : L2) :
    inner ℝ (FreeFlow.freeL2 t u) v = inner ℝ u (FreeFlow.freeL2 (-t) v) := by
  let U : L2 →ₗᵢ[ℝ] L2 :=
    { (FreeFlow.freeL2 t).toLinearMap.restrictScalars ℝ with norm_map' := FreeFlow.freeL2_norm t }
  have h := U.inner_map_map u (FreeFlow.freeL2 (-t) v)
  change inner ℝ (FreeFlow.freeL2 t u) (FreeFlow.freeL2 t (FreeFlow.freeL2 (-t) v)) = _ at h
  rwa [FreeFlow.freeL2_inverse] at h

variable (hDensity : OrdinaryH1Density) {K C : ℝ} (hSob : OrdinarySobolev K)
  (hS : OrdinaryHomogeneousStrichartz C)

include hDensity hSob hS in
theorem actual_freeSchwartz_L6_decay (φ : Test) {s : ℕ → ℝ}
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot) :
    Tendsto (fun n => ‖(FreeFlow.freeSchwartz (s n) φ).toLp 6 volume‖) atTop (𝓝 0) := by
  have h := FreeTimeDecay.freeEnergyState_schwartz_value_norm_decay hDensity hSob hS φ
  simp only [freeEnergyState_schwartz, schwartzEnergyState_value] at h
  rcases hs with hs | hs
  · exact h.1.comp hs
  · exact h.2.comp hs

/-- The exact linear map to an actual L2 coordinate gradient after physical affine
normalization and actual free evolution. -/
def terminalGradient (s r : ℝ) (hr : 0 < r) (y : V) (j : Fin 3) :
    EnergyState →L[ℂ] L2 :=
  (energyGradient j).comp ((freeEnergyCLM hDensity hSob s).comp
    (criticalAffineState r hr y).toLinearIsometry.toContinuousLinearMap)

theorem terminalGradient_apply (s r : ℝ) (hr : 0 < r) (y : V) (j : Fin 3) (f : EnergyState) :
    terminalGradient hDensity hSob s r hr y j f =
      energyGradient j (freeEnergyState hDensity hSob s (criticalAffineState r hr y f)) := rfl

theorem terminalGradient_norm (s r : ℝ) (hr : 0 < r) (y : V) (j : Fin 3) (f : EnergyState) :
    ‖terminalGradient hDensity hSob s r hr y j f‖ = ‖energyGradient j f‖ := by
  rw [terminalGradient_apply, freeEnergyState_gradient, FreeFlow.freeL2_norm]
  exact affineState_gradient_norm (inv_pos.mpr hr) (-(r⁻¹ • y)) f j

theorem terminalGradient_pair_lipschitz (s r : ℝ) (hr : 0 < r) (y : V) (j : Fin 3)
    (v : L2) (f g : EnergyState) :
    ‖inner ℝ (terminalGradient hDensity hSob s r hr y j f) v -
      inner ℝ (terminalGradient hDensity hSob s r hr y j g) v‖ ≤ ‖v‖ * ‖f-g‖ := by
  rw [← inner_sub_left, ← map_sub]
  have hb : ‖terminalGradient hDensity hSob s r hr y j (f-g)‖ ≤ ‖f-g‖ := by
    rw [terminalGradient_norm]
    exact energyState_gradient_norm_le (f-g) j
  have h := (norm_inner_le_norm (𝕜 := ℝ) (terminalGradient hDensity hSob s r hr y j (f-g)) v).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg v))
  simpa only [mul_comm] using h

include hS in
/-- Actual fixed Schwartz state and test decay under arbitrary centers and bounded
positive physical length scales. The scalar decay is produced from native free L6 decay. -/
theorem terminalGradient_schwartz_pair_zero
    (r s : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n ≤ 1) (y : ℕ → V)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot) (φ ψ : Test) (j : Fin 3) :
    Tendsto (fun n => inner ℝ
      (terminalGradient hDensity hSob (s n) (r n) (hr n) (y n) j (schwartzEnergyState φ))
      (ψ.toLp 2 volume)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => -s n) atTop atTop ∨ Tendsto (fun n => -s n) atTop atBot := by
    rcases hs with h | h
    · exact Or.inr (tendsto_neg_atTop_atBot.comp h)
    · exact Or.inl (tendsto_neg_atBot_atTop.comp h)
  have hd := (actual_freeSchwartz_L6_decay hDensity hSob hS ψ hn).const_mul
    (‖gradientSourcePair‖ * ‖(∂_{coordinate j} φ).toLp gradientSourceExponent volume‖)
  simp only [mul_zero] at hd
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hd
  intro n
  rw [terminalGradient_apply, freeEnergyState_gradient, actual_freeL2_real_adjoint,
    ← FreeFlow.freeSchwartz_toL2]
  have hb := criticalAffineSchwartzGradient_inner_bound (hr n) (y n) φ
    (FreeFlow.freeSchwartz (-s n) ψ) j
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) (hr1 n)) (norm_nonneg gradientSourcePair)) (norm_nonneg _))

include hS in
/-- Genuine finite Schwartz nets on the actual compact EnergyState carrier give
weak terminal zero for every fixed actual Schwartz L2 gradient test. -/
theorem compactOrbit_schwartz_gradient_zero
    (r s : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n ≤ 1) (y : ℕ → V)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot)
    {Q : Set EnergyState} (hQ : IsCompact Q) (f : ℕ → EnergyState) (hf : ∀ n, f n ∈ Q)
    (ψ : Test) (j : Fin 3) :
    Tendsto (fun n => inner ℝ
      (terminalGradient hDensity hSob (s n) (r n) (hr n) (y n) j (f n))
      (ψ.toLp 2 volume)) atTop (𝓝 0) :=
  compact_dense_uniform_zero (schwartzEnergyState_denseRange hDensity hSob)
    (fun n z => inner ℝ (terminalGradient hDensity hSob (s n) (r n) (hr n) (y n) j z)
      (ψ.toLp 2 volume)) (norm_nonneg _)
    (fun n x z => terminalGradient_pair_lipschitz hDensity hSob (s n) (r n) (hr n) (y n) j
      (ψ.toLp 2 volume) x z)
    (fun φ => terminalGradient_schwartz_pair_zero hDensity hSob hS r s hr hr1 y hs φ ψ j)
    hQ f (Filter.Eventually.of_forall hf)

end HartreeF.CompactOrbitTerminal
