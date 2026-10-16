import F121HalflineTerminal
import FLocalMildFiniteDuhamel

noncomputable section
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.OriginalSignedDuhamel
open EnergySpace MaximalTrajectory Retarded ForcingDomain CriticalAffine CompactOrbitTerminal
open SobolevStretch StationarySelfTest ActualStrichartz MassRecovery

theorem absolute_nplusone_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Proposition 6.5: full real-time weak zero and literal no-waste on one
absolute terminal sequence, for the same physical mild trajectory.
No forcing budget, terminal limit or finite formula is assumed. -/
theorem proposition65_halfline (hD : OrdinaryH1Density) {K C α c s₀ : ℝ}
    (hSob : OrdinarySobolev K) (hS : OrdinaryHomogeneousStrichartz C)
    (hH : OrdinaryHLS α c) {u₀ : EnergyState}
    (U : LocalMildTrajectory α c s₀ u₀)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hHalfline : ∀ s ∈ Ici (0 : ℝ), σ*s ∈ U.domain)
    (r : ℝ → ℝ) (y : ℝ → V)
    (hr : ∀ s ∈ Ici (0 : ℝ), 0 < r s) (hr1 : ∀ s ∈ Ici (0 : ℝ), r s ≤ 1)
    {Q : Set EnergyState} (hQ : IsCompact Q)
    (hq : ∀ s (hs : s ∈ Ici (0 : ℝ)),
      (criticalAffineState (r s) (hr s hs) (y s)).symm (U.state (σ*s)) ∈ Q) :
    (∀ L : EnergyState →L[ℝ] ℝ,
      Tendsto (fun T : ℝ => L (freeEnergyState hD hSob (σ*(0-T)) (U.state (σ*T))))
        atTop (𝓝 0)) ∧
    (∀ t ∈ Ici (0 : ℝ), ∀ φ : Test,
      Tendsto (fun n : ℕ => noWasteCoefficient σ * ∫ s in Icc t ((n : ℝ)+1), ∫ x : V,
        freeTest (σ*(t-s)) φ x * forcing α c (energyValue (U.state (σ*s))) x)
        atTop (𝓝 (energyDistribution (U.state (σ*t)) φ))) ∧
    (∀ t ∈ Ici (0 : ℝ), ∀ T : ℝ, t ≤ T → ∀ φ : Test,
      IntegrableOn (fun s => ∫ x : V,
        freeTest (σ*(t-s)) φ x * forcing α c (energyValue (U.state (σ*s))) x)
        (Icc t T) volume ∧
      energyDistribution (U.state (σ*t)) φ =
        energyDistribution (U.state (σ*T)) (freeTest (σ*(t-T)) φ) +
          noWasteCoefficient σ * ∫ s in Icc t T, ∫ x : V,
            freeTest (σ*(t-s)) φ x * forcing α c (energyValue (U.state (σ*s))) x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L
    exact halfline_real_dual_zero hD hSob hS (fun s => U.state (σ*s)) r y hr hr1 hQ hq hσ 0 L
  · intro t ht φ
    have hz := (halfline_real_tested_zero hD hSob hS (fun s => U.state (σ*s))
      r y hr hr1 hQ hq hσ t φ).comp absolute_nplusone_tendsto
    have hl : Tendsto (fun n : ℕ => energyDistribution (U.state (σ*t)) φ -
        energyDistribution (U.state (σ*((n : ℝ)+1))) (freeTest (σ*(t-((n : ℝ)+1))) φ))
        atTop (𝓝 (energyDistribution (U.state (σ*t)) φ)) := by
      simpa only [sub_zero, Function.comp_apply] using
        (tendsto_const_nhds (x := energyDistribution (U.state (σ*t)) φ)).sub hz
    apply hl.congr'
    have hlarge : ∀ᶠ n : ℕ in atTop, t ≤ (n : ℝ)+1 :=
      absolute_nplusone_tendsto.eventually (eventually_ge_atTop t)
    filter_upwards [hlarge] with n hn
    have he := local_mild_signed_finite U hσ hn
      (fun s hs => hHalfline s (ht.trans hs.1)) φ
    exact sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _))
  · intro t ht T hT φ
    exact ⟨local_mild_signed_window_integrable U hD hSob hH hσ hT
      (fun s hs => hHalfline s (ht.trans hs.1)) φ,
      local_mild_signed_finite U hσ hT (fun s hs => hHalfline s (ht.trans hs.1)) φ⟩

end HartreeF.OriginalSignedDuhamel
