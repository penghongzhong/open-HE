import FCompactOrbitGradientTerminal
import FRetardedScalarL2

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set LineDeriv
open scoped ENNReal Topology SchwartzMap RealInnerProductSpace
namespace HartreeF.CompactOrbitTerminal
open EnergySpace CriticalAffine SobolevStretch StationarySelfTest ActualStrichartz Retarded
attribute [local irreducible] energySubmodule
variable (hDensity : OrdinaryH1Density) {K C : ℝ} (hSob : OrdinarySobolev K)
  (hS : OrdinaryHomogeneousStrichartz C)

include hDensity hSob hS in
theorem actual_freeSchwartz_L6_decay_real (φ : Test) {s : ℝ → ℝ}
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot) :
    Tendsto (fun n => ‖(FreeFlow.freeSchwartz (s n) φ).toLp 6 volume‖) atTop (𝓝 0) := by
  have h := FreeTimeDecay.freeEnergyState_schwartz_value_norm_decay hDensity hSob hS φ
  simp only [freeEnergyState_schwartz, schwartzEnergyState_value] at h
  rcases hs with hs | hs
  · exact h.1.comp hs
  · exact h.2.comp hs

include hS in
/-- Actual fixed Schwartz state and test decay under arbitrary centers and bounded
positive physical length scales. The scalar decay is produced from native free L6 decay. -/
theorem terminalGradient_schwartz_pair_zero_real
    (r s : ℝ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n ≤ 1) (y : ℝ → V)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot) (φ ψ : Test) (j : Fin 3) :
    Tendsto (fun n => inner ℝ
      (terminalGradient hDensity hSob (s n) (r n) (hr n) (y n) j (schwartzEnergyState φ))
      (ψ.toLp 2 volume)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n => -s n) atTop atTop ∨ Tendsto (fun n => -s n) atTop atBot := by
    rcases hs with h | h
    · exact Or.inr (tendsto_neg_atTop_atBot.comp h)
    · exact Or.inl (tendsto_neg_atBot_atTop.comp h)
  have hd := (actual_freeSchwartz_L6_decay_real hDensity hSob hS ψ hn).const_mul
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
theorem compactOrbit_schwartz_gradient_zero_real
    (r s : ℝ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n ≤ 1) (y : ℝ → V)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot)
    {Q : Set EnergyState} (hQ : IsCompact Q) (f : ℝ → EnergyState) (hf : ∀ n, f n ∈ Q)
    (ψ : Test) (j : Fin 3) :
    Tendsto (fun n => inner ℝ
      (terminalGradient hDensity hSob (s n) (r n) (hr n) (y n) j (f n))
      (ψ.toLp 2 volume)) atTop (𝓝 0) :=
  compact_dense_uniform_zero (schwartzEnergyState_denseRange hDensity hSob)
    (fun n z => inner ℝ (terminalGradient hDensity hSob (s n) (r n) (hr n) (y n) j z)
      (ψ.toLp 2 volume)) (norm_nonneg _)
    (fun n x z => terminalGradient_pair_lipschitz hDensity hSob (s n) (r n) (hr n) (y n) j
      (ψ.toLp 2 volume) x z)
    (fun φ => terminalGradient_schwartz_pair_zero_real hDensity hSob hS r s hr hr1 y hs φ ψ j)
    hQ f (Filter.Eventually.of_forall hf)

include hS in
/-- L2 test density plus the compact carrier's DERIVED norm bound produces full
coordinate weak convergence. No uniform-gradient bound is added as a premise. -/
theorem compactOrbit_gradient_zero_real
    (r s : ℝ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n ≤ 1) (y : ℝ → V)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot)
    {Q : Set EnergyState} (hQ : IsCompact Q) (f : ℝ → EnergyState) (hf : ∀ n, f n ∈ Q)
    (v : L2) (j : Fin 3) :
    Tendsto (fun n => inner ℝ
      (terminalGradient hDensity hSob (s n) (r n) (hr n) (y n) j (f n)) v) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := hQ.isBounded.exists_pos_norm_le
  apply dense_uniform_lipschitz_zero
    (SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ) (p := 2) (μ := volume) (by norm_num))
    (fun n w => inner ℝ (terminalGradient hDensity hSob (s n) (r n) (hr n) (y n) j (f n)) w)
    hB.le ?_ ?_ v
  · intro n w z
    rw [← inner_sub_right]
    apply (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [terminalGradient_norm]
    exact (energyState_gradient_norm_le (f n) j).trans (hbound (f n) (hf n))
  · intro ψ
    exact compactOrbit_schwartz_gradient_zero_real hDensity hSob hS r s hr hr1 y hs hQ f hf ψ j

include hS in
/-- Every continuous real functional on the SAME original EnergyState tends to zero;
the actual gradient-dual representation is used rather than assumed weak state convergence. -/
theorem compactOrbit_energy_dual_zero_real
    (r s : ℝ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n ≤ 1) (y : ℝ → V)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot)
    {Q : Set EnergyState} (hQ : IsCompact Q) (f : ℝ → EnergyState) (hf : ∀ n, f n ∈ Q)
    (L : EnergyState →L[ℝ] ℝ) :
    Tendsto (fun n => L (freeEnergyState hDensity hSob (s n)
      (criticalAffineState (r n) (hr n) (y n) (f n)))) atTop (𝓝 0) := by
  have hw : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (freeEnergyState hDensity hSob (s n)
        (criticalAffineState (r n) (hr n) (y n) (f n)))) v) atTop
        (𝓝 (inner ℝ (energyGradient j (0 : EnergyState)) v)) := by
    intro j v
    simpa only [map_zero, inner_zero_left, terminalGradient_apply] using
      compactOrbit_gradient_zero_real hDensity hSob hS r s hr hr1 y hs hQ f hf v j
  obtain ⟨w, hwL⟩ := LocalRellich.energyState_dual_gradient_representation hSob L
  simpa only [hwL, map_zero, inner_zero_left, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun j _ => hw j (w j))

include hS in
/-- Actual Schwartz distribution evaluation is a complex continuous functional;
its real and imaginary parts use the produced original-state weak limit. -/
theorem compactOrbit_distribution_zero_real
    (r s : ℝ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n ≤ 1) (y : ℝ → V)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot)
    {Q : Set EnergyState} (hQ : IsCompact Q) (f : ℝ → EnergyState) (hf : ∀ n, f n ∈ Q)
    (φ : Test) :
    Tendsto (fun n => energyDistribution (freeEnergyState hDensity hSob (s n)
      (criticalAffineState (r n) (hr n) (y n) (f n))) φ) atTop (𝓝 0) := by
  let L : EnergyState →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution
  have hre := compactOrbit_energy_dual_zero_real hDensity hSob hS r s hr hr1 y hs hQ f hf
    (Complex.reCLM.comp (L.restrictScalars ℝ))
  have him := compactOrbit_energy_dual_zero_real hDensity hSob hS r s hr hr1 y hs hQ f hf
    (Complex.imCLM.comp (L.restrictScalars ℝ))
  let z : ℝ → ℂ := fun n => energyDistribution (freeEnergyState hDensity hSob (s n)
    (criticalAffineState (r n) (hr n) (y n) (f n))) φ
  change Tendsto (fun n => (z n).re) atTop (𝓝 0) at hre
  change Tendsto (fun n => (z n).im) atTop (𝓝 0) at him
  have hreC := Complex.continuous_ofReal.tendsto 0 |>.comp hre
  have himC := Complex.continuous_ofReal.tendsto 0 |>.comp him
  have h := hreC.add (himC.mul_const Complex.I)
  simpa only [Function.comp_apply, Complex.re_add_im, Complex.ofReal_zero, zero_mul, zero_add] using h

include hDensity hSob hS in
/-- The free term is literally the original distribution paired with the exact
FRetardedScalarL2 freeTest, including its bilinear transpose convention. -/
theorem compactOrbit_tested_terminal_zero_real
    (r s : ℝ → ℝ) (hr : ∀ n, 0 < r n) (hr1 : ∀ n, r n ≤ 1) (y : ℝ → V)
    (hs : Tendsto s atTop atTop ∨ Tendsto s atTop atBot)
    {Q : Set EnergyState} (hQ : IsCompact Q) (f : ℝ → EnergyState) (hf : ∀ n, f n ∈ Q)
    (φ : Test) :
    Tendsto (fun n => energyDistribution (criticalAffineState (r n) (hr n) (y n) (f n))
      (freeTest (s n) φ)) atTop (𝓝 0) := by
  simpa only [freeEnergyState_distribution, free_apply] using
    compactOrbit_distribution_zero_real hDensity hSob hS r s hr hr1 y hs hQ f hf φ

end HartreeF.CompactOrbitTerminal
