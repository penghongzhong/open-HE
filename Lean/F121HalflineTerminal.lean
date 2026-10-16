import F121RealCompactTerminal

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.CompactOrbitTerminal
open EnergySpace CriticalAffine SobolevStretch StationarySelfTest ActualStrichartz Retarded

theorem real_terminal_free_time_escape {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) :
    Tendsto (fun T : ℝ => σ*(t-T)) atTop atTop ∨
      Tendsto (fun T : ℝ => σ*(t-T)) atTop atBot := by
  have h : Tendsto (fun T : ℝ => T-t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b+t)] with T hT
    linarith
  rcases hσ with rfl | rfl
  · right
    convert tendsto_neg_atTop_atBot.comp h using 1
    funext T
    simp only [Function.comp_apply]
    ring
  · left
    convert h using 1
    funext T
    ring

/-- Full real-time weak terminal limit of the same half-orbit. -/
theorem halfline_real_dual_zero (hD : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (u : ℝ → EnergyState) (r : ℝ → ℝ) (y : ℝ → V)
    (hr : ∀ s ∈ Ici (0 : ℝ), 0 < r s) (hr1 : ∀ s ∈ Ici (0 : ℝ), r s ≤ 1)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hq : ∀ s (hs : s ∈ Ici (0 : ℝ)),
      (criticalAffineState (r s) (hr s hs) (y s)).symm (u s) ∈ Q)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) (L : EnergyState →L[ℝ] ℝ) :
    Tendsto (fun T : ℝ => L (freeEnergyState hD hSob (σ*(t-T)) (u T))) atTop (𝓝 0) := by
  classical
  let R : ℝ → ℝ := fun T => if 0 ≤ T then r T else 1
  have hR (T : ℝ) : 0 < R T := by
    dsimp [R]
    split_ifs with hT
    · exact hr T hT
    · norm_num
  have hR1 (T : ℝ) : R T ≤ 1 := by
    dsimp [R]
    split_ifs with hT
    · exact hr1 T hT
    · exact le_rfl
  let f : ℝ → EnergyState := fun T => if hT : 0 ≤ T then
    (criticalAffineState (r T) (hr T hT) (y T)).symm (u T) else 0
  have hf (T : ℝ) : f T ∈ insert (0 : EnergyState) Q := by
    dsimp [f]
    split_ifs with hT
    · exact mem_insert_of_mem _ (hq T hT)
    · exact mem_insert _ _
  have hz := compactOrbit_energy_dual_zero_real hD hSob hS R (fun T => σ*(t-T))
    hR hR1 y (real_terminal_free_time_escape hσ t) (hQ.insert 0) f hf L
  apply hz.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  dsimp [R, f]
  simp only [dite_eq_left hT, ite_eq_left hT, LinearIsometryEquiv.apply_symm_apply]

/-- The real terminal limit also gives every actual distribution test. -/
theorem halfline_real_tested_zero (hD : OrdinaryH1Density) {K C : ℝ}
    (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (u : ℝ → EnergyState) (r : ℝ → ℝ) (y : ℝ → V)
    (hr : ∀ s ∈ Ici (0 : ℝ), 0 < r s) (hr1 : ∀ s ∈ Ici (0 : ℝ), r s ≤ 1)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hq : ∀ s (hs : s ∈ Ici (0 : ℝ)),
      (criticalAffineState (r s) (hr s hs) (y s)).symm (u s) ∈ Q)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (t : ℝ) (φ : Test) :
    Tendsto (fun T : ℝ => energyDistribution (u T) (freeTest (σ*(t-T)) φ)) atTop (𝓝 0) := by
  let L : EnergyState →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution
  have hre := halfline_real_dual_zero hD hSob hS u r y hr hr1 hQ hq hσ t
    (Complex.reCLM.comp (L.restrictScalars ℝ))
  have him := halfline_real_dual_zero hD hSob hS u r y hr hr1 hQ hq hσ t
    (Complex.imCLM.comp (L.restrictScalars ℝ))
  let z : ℝ → ℂ := fun T => energyDistribution
    (freeEnergyState hD hSob (σ*(t-T)) (u T)) φ
  change Tendsto (fun T => (z T).re) atTop (𝓝 0) at hre
  change Tendsto (fun T => (z T).im) atTop (𝓝 0) at him
  have hreC := Complex.continuous_ofReal.tendsto 0 |>.comp hre
  have himC := Complex.continuous_ofReal.tendsto 0 |>.comp him
  have h := hreC.add (himC.mul_const Complex.I)
  simpa only [Function.comp_apply, Complex.re_add_im, Complex.ofReal_zero, zero_mul,
    zero_add, z, freeEnergyState_distribution, free_apply] using h

end HartreeF.CompactOrbitTerminal
