import FActualProfileEnergyLedger

/-! UNCOMPILED authorized source draft. One eligible depth J0 = j0 + 1
is fixed before its energy subsequence. All data and frame coordinates use
the same returned map. This is full-frame concentration, with no exclusion
of either infinite normalized-time regime. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace HartreeF.ActualProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput
open StateEnergy StateSharpThreshold SharpOrdinary ForcingDomain
open MaximalTrajectory ProfileEnergy FreeTimeDecay
attribute [local irreducible] energySubmodule

/-- Once the scalar allocation consumer identifies one full-energy label and
all other actual linear profiles vanish, the same family concentrates along
one fixed-depth energy subsequence in pure-gradient and actual graph norms. -/
theorem single_profile_concentration (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha E0 : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (T : ℕ → ℝ) (f : ℕ → EnergyState)
    (L : ProfileEnergyLedger hDensity hSob h0 hfree hret hefree heret hOrd P u T f E0)
    (hE : Tendsto (fun n => totalEnergy alpha (u n)) atTop (𝓝 E0))
    (j0 : ℕ) (hj0 : (j0 : WithTop ℕ) < P.count)
    (hcrit : totalEnergy alpha (f j0) = E0)
    (hother : ∀ j, j ≠ j0 → P.profile j = 0) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      Tendsto (fun n => pureGradientNorm
        (u (τ n) - profileAtom hDensity hSob P j0 (τ n))) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖u (τ n) - profileAtom hDensity hSob P j0 (τ n)‖) atTop (𝓝 0) := by
  classical
  let J0 := j0 + 1
  have hJ0 : (J0 : WithTop ℕ) ≤ P.count := active_succ_eligible P j0 hj0
  have hjmem : j0 ∈ Finset.range J0 := Finset.mem_range.mpr (Nat.lt_succ_self j0)
  have hzero : totalEnergy alpha (0 : EnergyState) = 0 := by
    simp [totalEnergy, gradientSquared, interactionLp_zero hH.order_pos]
  have hsum (n : ℕ) : (∑ j ∈ Finset.range J0, profileAtom hDensity hSob P j n) =
      profileAtom hDensity hSob P j0 n := by
    apply Finset.sum_eq_single j0
    · intro j _ hj
      simp only [profileAtom, hother j hj, map_zero]
    · intro hj
      exact (hj hjmem).elim
  have hsumE (n : ℕ) : (∑ j ∈ Finset.range J0, totalEnergy alpha (profileAtom hDensity hSob P j n)) =
      totalEnergy alpha (profileAtom hDensity hSob P j0 n) := by
    apply Finset.sum_eq_single j0
    · intro j _ hj
      simp only [profileAtom, hother j hj, map_zero, hzero]
    · intro hj
      exact (hj hjmem).elim
  have hr_eq (n : ℕ) : profileRemainder hDensity hSob P u J0 n =
      u n - profileAtom hDensity hSob P j0 n := by
    simp only [profileRemainder, hsum n]
  obtain ⟨τ, hτ, hdef⟩ := L.finite_energy_subsequence J0 hJ0
  have ha : Tendsto (fun n => totalEnergy alpha (profileAtom hDensity hSob P j0 (τ n)))
      atTop (𝓝 E0) := by
    simpa only [hcrit] using (L.atom_energy_limit j0).comp hτ.tendsto_atTop
  have hrE : Tendsto (fun n => totalEnergy alpha (profileRemainder hDensity hSob P u J0 (τ n)))
      atTop (𝓝 0) := by
    have ht := ((hE.comp hτ.tendsto_atTop).sub ha).sub hdef
    simp only [sub_self, sub_zero, hsumE] at ht
    convert ht using 1
    funext n
    ring
  have hbound : ∀ᶠ n in atTop,
      gradientSquared (profileRemainder hDensity hSob P u J0 (τ n)) ≤
        kappa alpha * totalEnergy alpha (profileRemainder hDensity hSob P u J0 (τ n)) := by
    filter_upwards [hτ.tendsto_atTop.eventually (L.remainder_eventually_below J0 hJ0)] with n hn
    exact state_kinetic_le_energy_below_W hOrd hH hS
      (profileRemainder hDensity hSob P u J0 (τ n)) hn.le
  have hrA : Tendsto (fun n => gradientSquared (profileRemainder hDensity hSob P u J0 (τ n)))
      atTop (𝓝 0) := by
    have ht : Tendsto (fun n => kappa alpha *
        totalEnergy alpha (profileRemainder hDensity hSob P u J0 (τ n))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hrE.const_mul (kappa alpha)
    exact squeeze_zero' (Eventually.of_forall (fun n => gradientSquared_nonneg _)) hbound ht
  have hrP : Tendsto (fun n => pureGradientNorm (profileRemainder hDensity hSob P u J0 (τ n)))
      atTop (𝓝 0) := by
    simpa only [pureGradientNorm, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hrA
  have hrN : Tendsto (fun n => ‖profileRemainder hDensity hSob P u J0 (τ n)‖)
      atTop (𝓝 0) := by
    have ht : Tendsto (fun n => max (K ^ ((6 : ℝ)⁻¹)) 1 *
        pureGradientNorm (profileRemainder hDensity hSob P u J0 (τ n))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hrP.const_mul (max (K ^ ((6 : ℝ)⁻¹)) 1)
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => energyState_le_pureGradient hSob _) ht
  exact ⟨τ, hτ, by simpa only [hr_eq] using hrP, by simpa only [hr_eq] using hrN⟩

/-- A full inverse linear frame preserves the pure-gradient error exactly;
graph convergence follows with the fixed Sobolev comparison constant. -/
theorem inverse_full_frame_concentration (hDensity : OrdinaryH1Density)
    {K : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (j : ℕ) (τ : ℕ → ℕ)
    (hconv : Tendsto (fun n => pureGradientNorm
      (u (τ n) - profileAtom hDensity hSob P j (τ n))) atTop (𝓝 0)) :
    Tendsto (fun n => pureGradientNorm
      ((linearProfileFrame hDensity hSob (P.scale j (τ n)) (P.scale_pos j (τ n))
        (P.center j (τ n)) (P.time j (τ n))).symm (u (τ n)) - P.profile j)) atTop (𝓝 0) ∧
    Tendsto (fun n => ‖(linearProfileFrame hDensity hSob (P.scale j (τ n)) (P.scale_pos j (τ n))
      (P.center j (τ n)) (P.time j (τ n))).symm (u (τ n)) - P.profile j‖) atTop (𝓝 0) := by
  let A := fun n => linearProfileFrame hDensity hSob (P.scale j (τ n)) (P.scale_pos j (τ n))
    (P.center j (τ n)) (P.time j (τ n))
  let d := fun n => (A n).symm (u (τ n)) - P.profile j
  have he (n : ℕ) : A n (d n) = u (τ n) - profileAtom hDensity hSob P j (τ n) := by
    simp only [d, map_sub, ContinuousLinearEquiv.apply_symm_apply, A, profileAtom]
  have hp : Tendsto (fun n => pureGradientNorm (d n)) atTop (𝓝 0) := by
    have heP (n : ℕ) : pureGradientNorm (d n) =
        pureGradientNorm (u (τ n) - profileAtom hDensity hSob P j (τ n)) := by
      rw [← he n]
      exact (linearProfileFrame_pureGradientNorm hDensity hSob _ _ _ _ _).symm
    simpa only [heP] using hconv
  refine ⟨hp, ?_⟩
  have ht : Tendsto (fun n => max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm (d n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul (max (K ^ ((6 : ℝ)⁻¹)) 1)
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => energyState_le_pureGradient hSob _) ht

end HartreeF.ActualProfileEnergy
