import FFiniteLinearProfileEnergy
import FCountableActualNonlinearProfiles
import FActualMaximalMildEnergyConservation
import FActualDynamicSharpWTrapping
import FFreeHartreeEnergyTails
import FSmallSTailContinuation

/-! UNCOMPILED authorized source draft. All energy limits concern the same
selected family and matching witnesses. Fixed-prefix energy extractions are
used only for scalar allocation; no all-depth energy diagonal is asserted. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace HartreeF.ActualProfileEnergy
open EnergySpace SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput
open StateEnergy StateSharpThreshold SharpOrdinary LocalRellich ForcingDomain
open MaximalTrajectory CountableNonlinearProfiles ProfileEnergy CommonProfileTimes
open Regularization.Actual FreeTimeDecay DynamicSharpW
attribute [local irreducible] energySubmodule

def kappa (alpha : ℝ) : ℝ := 2*(3+alpha)/(2+alpha)

theorem kappa_pos {alpha : ℝ} (ha : 0 < alpha) : 0 < kappa alpha := by
  unfold kappa
  positivity

/-- An active label belongs to its actual eligible successor prefix. -/
theorem active_succ_eligible (P : LinearProfileFamily) (j : ℕ)
    (hj : (j : WithTop ℕ) < P.count) : ((j+1 : ℕ) : WithTop ℕ) ≤ P.count := by
  cases hcount : P.count with
  | top => simp
  | coe N =>
    have hjN : j < N := by simpa [hcount] using hj
    exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt hjN)

/-- The sharp kinetic prefix bound uses the limiting energy and does not
assume convergence of the original kinetic sequence. -/
theorem kinetic_prefix_and_remainder (hDensity : OrdinaryH1Density)
    {K alpha E0 : ℝ} (hSob : OrdinarySobolev K) (P : LinearProfileFamily)
    (u : ℕ → EnergyState) (hP : LinearProfileProperties hDensity hSob u P)
    (hE : Tendsto (fun n => totalEnergy alpha (u n)) atTop (𝓝 E0))
    (hkin : ∀ n, gradientSquared (u n) ≤ kappa alpha * totalEnergy alpha (u n))
    (hgap : kappa alpha * E0 < gradientSquared (normalizedBubbleState alpha))
    (J : ℕ) (hJ : (J : WithTop ℕ) ≤ P.count) :
    (∑ j ∈ Finset.range J, gradientSquared (P.profile j)) ≤ kappa alpha * E0 ∧
    (∀ᶠ n in atTop, gradientSquared (profileRemainder hDensity hSob P u J n) <
      gradientSquared (normalizedBubbleState alpha)) := by
  let q := ∑ j ∈ Finset.range J, gradientSquared (P.profile j)
  let d := fun n => gradientSquared (u n) - q -
    gradientSquared (profileRemainder hDensity hSob P u J n)
  have hd : Tendsto d atTop (𝓝 0) := hP.kinetic J hJ
  have hb : Tendsto (fun n => kappa alpha * totalEnergy alpha (u n) - d n)
      atTop (𝓝 (kappa alpha * E0)) := by
    simpa only [sub_zero] using (hE.const_mul (kappa alpha)).sub hd
  have hq : 0 ≤ q := Finset.sum_nonneg (fun j _ => gradientSquared_nonneg _)
  have hp : q ≤ kappa alpha * E0 := by
    apply ge_of_tendsto hb
    exact Eventually.of_forall (fun n => by
      have hr := gradientSquared_nonneg (profileRemainder hDensity hSob P u J n)
      dsimp [d]
      linarith [hkin n])
  refine ⟨hp, ?_⟩
  filter_upwards [hb.eventually (gt_mem_nhds hgap)] with n hn
  dsimp [d] at hn
  linarith [hkin n]

/-- The actual finite/positive-infinite/negative-infinite branch bodies yield
a free energy limit. Finite normalized times retain their actual free state. -/
theorem free_profile_energy_has_limit (hDensity : OrdinaryH1Density)
    {K Ch alpha : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (phi : EnergyState) (s : ℕ → ℝ) (hs : TimeRegime s) :
    ∃ L : ℝ, Tendsto (fun n => totalEnergy alpha (freeEnergyState hDensity hSob (s n) phi))
      atTop (𝓝 L) := by
  rcases hs with ⟨t, ht⟩ | hp | hn
  · exact ⟨totalEnergy alpha (freeEnergyState hDensity hSob t phi),
      totalEnergy_tendsto hOrd (finite_free_atom_strong hDensity hSob phi ht).1⟩
  · exact ⟨gradientSquared phi / 2,
      (freeEnergyState_totalEnergy_tendsto_kinetic_atTop hDensity hSob hfree hOrd phi).comp hp⟩
  · exact ⟨gradientSquared phi / 2,
      (freeEnergyState_totalEnergy_tendsto_kinetic_atBot hDensity hSob hfree hOrd phi).comp hn⟩

/-- For one label only, replace a finite initial segment by zero. This
supplies the all-index graph bounds required by moving energy continuity.
The selected curve and every time/frame parameter remain unchanged. -/
theorem single_matching_limits (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (T : ℝ) (f phi : EnergyState) (s : ℕ → ℝ)
    (hdom : ∀ᶠ n in atTop, s n ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd T f).domain)
    (hmatch : Tendsto (fun n => ‖
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd T f).state (s n) -
      freeEnergyState hDensity hSob (s n) phi‖) atTop (𝓝 0)) :
    Tendsto (fun n => totalEnergy alpha (freeEnergyState hDensity hSob (s n) phi))
      atTop (𝓝 (totalEnergy alpha f)) ∧
    Tendsto (fun n => gradientSquared
      ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd T f).state (s n)))
      atTop (𝓝 (gradientSquared phi)) := by
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd T f
  let v := fun n => freeEnergyState hDensity hSob (s n) phi
  let C := max (K ^ ((6 : ℝ)⁻¹)) 1 * pureGradientNorm phi
  have hC : 0 ≤ C := mul_nonneg ((show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_right _ _))
    (pureGradientNorm_nonneg phi)
  have hv (n : ℕ) : ‖v n‖ ≤ C := by
    simpa only [v, C, freeEnergyState_pureGradientNorm] using energyState_le_pureGradient hSob (v n)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hdom.and (hmatch.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))))
  let w := fun n => if N ≤ n then M.state (s n) else 0
  have hw (n : ℕ) : ‖w n‖ ≤ 1 + C := by
    by_cases hn : N ≤ n
    · have he := (hN n hn).2
      calc
        ‖w n‖ = ‖(M.state (s n) - v n) + v n‖ := by simp [w, hn, v]
        _ ≤ ‖M.state (s n) - v n‖ + ‖v n‖ := norm_add_le _ _
        _ ≤ 1 + C := add_le_add he.le (hv n)
    · simp only [w, ite_eq_right hn, norm_zero]
      linarith
  have hv' (n : ℕ) : ‖v n‖ ≤ 1 + C := (hv n).trans (by linarith)
  have heq : w =ᶠ[atTop] (fun n => M.state (s n)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [w, ite_eq_left hn]
  have hd : Tendsto (fun n => ‖w n - v n‖) atTop (𝓝 0) := by
    apply hmatch.congr'
    filter_upwards [heq] with n hn
    simp only [hn, v, M]
  have hwd : Tendsto (fun n => totalEnergy alpha (w n) - totalEnergy alpha (v n))
      atTop (𝓝 0) := totalEnergy_difference_tendsto_zero hH hOrd hw hv' hd
  have hwe : Tendsto (fun n => totalEnergy alpha (w n))
      atTop (𝓝 (totalEnergy alpha f)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq, hdom] with n hn hm
    rw [hn]
    exact (actualMaximalTrajectory_totalEnergy_constant hDensity hSob h0 hfree hret
      hefree heret hOrd S Bw Bs B6 T f (s n) hm).symm
  have hve : Tendsto (fun n => totalEnergy alpha (v n))
      atTop (𝓝 (totalEnergy alpha f)) := by
    convert hwe.sub hwd using 1 <;> try simp only [sub_zero]
    funext n
    ring
  have hgd := gradientSquared_difference_tendsto_zero hw hv' hd
  have hgw : Tendsto (fun n => gradientSquared (w n)) atTop (𝓝 (gradientSquared phi)) := by
    have hh := hgd.add_const (gradientSquared phi)
    simpa only [v, freeEnergyState_gradientSquared, sub_add_cancel, zero_add] using hh
  refine ⟨hve, ?_⟩
  apply hgw.congr'
  filter_upwards [heq] with n hn
  rw [hn]

/-- Exact family contract. The stable matching state and native trapping
refer to the original selected canonical trajectories. -/
structure ProfileEnergyLedger (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (T : ℕ → ℝ)
    (f : ℕ → EnergyState) (E0 : ℝ) : Prop where
  energy_nonneg : ∀ j, 0 ≤ totalEnergy alpha (f j)
  energy_le : ∀ j, totalEnergy alpha (f j) ≤ E0
  kinetic_le_energy : ∀ j, gradientSquared (P.profile j) ≤ kappa alpha * totalEnergy alpha (f j)
  zero_energy : ∀ j, P.profile j = 0 → totalEnergy alpha (f j) = 0
  atom_energy_limit : ∀ j, Tendsto (fun n => totalEnergy alpha (profileAtom hDensity hSob P j n))
    atTop (𝓝 (totalEnergy alpha (f j)))
  kinetic_prefix : ∀ J : ℕ, (J : WithTop ℕ) ≤ P.count →
    (∑ j ∈ Finset.range J, gradientSquared (P.profile j)) ≤ kappa alpha * E0
  remainder_eventually_below : ∀ J : ℕ, (J : WithTop ℕ) ≤ P.count → ∀ᶠ n in atTop,
    gradientSquared (profileRemainder hDensity hSob P u J n) < gradientSquared (normalizedBubbleState alpha)
  finite_energy_subsequence : ∀ J : ℕ, (J : WithTop ℕ) ≤ P.count →
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ Tendsto (fun n => totalEnergy alpha (u (τ n)) -
      totalEnergy alpha (profileRemainder hDensity hSob P u J (τ n)) -
      ∑ j ∈ Finset.range J, totalEnergy alpha (profileAtom hDensity hSob P j (τ n))) atTop (𝓝 0)
  allocation : ∀ J : ℕ, (J : WithTop ℕ) ≤ P.count →
    (∑ j ∈ Finset.range J, totalEnergy alpha (f j)) ≤ E0
  stable_state : ∀ j, ∃ t : ℝ,
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd (T j) (f j)
    t ∈ M.domain ∧ totalEnergy alpha (M.state t) = totalEnergy alpha (f j) ∧
    totalEnergy alpha (M.state t) < totalEnergy alpha (normalizedBubbleState alpha) ∧
    pureGradientNorm (M.state t) < pureGradientNorm (normalizedBubbleState alpha)
  native_trapping : ∀ j t,
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd (T j) (f j)
    t ∈ M.domain → gradientSquared (M.state t) ≤ kappa alpha * totalEnergy alpha (f j) ∧
      kappa alpha * totalEnergy alpha (f j) < gradientSquared (normalizedBubbleState alpha)

/-- The ledger is produced from ordinary interfaces, actual matching and
conservation. The rough all-index cap is separate from eventual sharp bounds. -/
theorem build_profile_energy_ledger (hDensity : OrdinaryH1Density)
    (hRel : OrdinaryRellichBall) {K C0 Ch Cr Che Cre alpha E0 B : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (HeatRiesz.standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (P : LinearProfileFamily) (u : ℕ → EnergyState) (T : ℕ → ℝ) (f : ℕ → EnergyState)
    (hP : LinearProfileProperties hDensity hSob u P)
    (ht : ∀ j, TimeRegime (P.time j))
    (hA : ActualProfileFamilyApproximation hDensity hSob h0 hfree hret hefree heret hOrd P T f)
    (hB : ∀ n, pureGradientNorm (u n) ≤ B)
    (hE : Tendsto (fun n => totalEnergy alpha (u n)) atTop (𝓝 E0))
    (hkin : ∀ n, gradientSquared (u n) ≤ kappa alpha * totalEnergy alpha (u n))
    (hgap : kappa alpha * E0 < gradientSquared (normalizedBubbleState alpha))
    (hEW : E0 < totalEnergy alpha (normalizedBubbleState alpha)) :
    ProfileEnergyLedger hDensity hSob h0 hfree hret hefree heret hOrd P u T f E0 := by
  have hkpos : 0 < kappa alpha := kappa_pos hH.order_pos
  have hprefix := kinetic_prefix_and_remainder hDensity hSob P u hP hE hkin hgap
  have hE0 : 0 ≤ E0 := by
    have hh := (hprefix 0 (by simp)).1
    simp only [Finset.range_zero, Finset.sum_empty] at hh
    nlinarith
  have hphi (j : ℕ) : gradientSquared (P.profile j) ≤ kappa alpha * E0 := by
    by_cases hj : (j : WithTop ℕ) < P.count
    · exact (Finset.single_le_sum (fun k _ => gradientSquared_nonneg (P.profile k))
        (Finset.mem_range.mpr (Nat.lt_succ_self j))).trans
        (hprefix (j+1) (active_succ_eligible P j hj)).1
    · rw [P.inactive_zero j hj]
      simp only [gradientSquared, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero]
      exact mul_nonneg hkpos.le hE0
  have hmatch (j : ℕ) := single_matching_limits hDensity hSob h0 hfree hret hefree heret
    hOrd hH S Bw Bs B6 (T j) (f j) (P.profile j) (P.time j) (hA j).1 (hA j).2
  have hatom (j : ℕ) : Tendsto (fun n => totalEnergy alpha (profileAtom hDensity hSob P j n))
      atTop (𝓝 (totalEnergy alpha (f j))) := by
    obtain ⟨L, hL⟩ := free_profile_energy_has_limit hDensity hSob hfree hOrd
      (P.profile j) (P.time j) (ht j)
    have hLe : L = totalEnergy alpha (f j) := tendsto_nhds_unique hL (hmatch j).1
    rw [hLe] at hL
    simpa only [profileAtom, linearProfileFrame_totalEnergy hDensity hSob hOrd] using hL
  have hco (j : ℕ) : gradientSquared (P.profile j) ≤ kappa alpha * totalEnergy alpha (f j) := by
    apply ge_of_tendsto ((hatom j).const_mul (kappa alpha))
    apply Eventually.of_forall
    intro n
    have hb : gradientSquared (profileAtom hDensity hSob P j n) ≤
        gradientSquared (normalizedBubbleState alpha) := by
      simpa only [profileAtom, linearProfileFrame_gradientSquared] using (hphi j).trans hgap.le
    simpa only [profileAtom, linearProfileFrame_gradientSquared, kappa] using
      state_kinetic_le_energy_below_W hOrd hH hS (profileAtom hDensity hSob P j n) hb
  have henon (j : ℕ) : 0 ≤ totalEnergy alpha (f j) := by
    have hg := gradientSquared_nonneg (P.profile j)
    nlinarith [hco j]
  have hzero (j : ℕ) (hz : P.profile j = 0) : totalEnergy alpha (f j) = 0 := by
    have hezero : totalEnergy alpha (0 : EnergyState) = 0 := by
      simp [totalEnergy, gradientSquared, interactionLp_zero hH.order_pos]
    have hh : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (totalEnergy alpha (f j))) := by
      simpa only [profileAtom, hz, map_zero, hezero] using hatom j
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hsplit (J : ℕ) (hJ : (J : WithTop ℕ) ≤ P.count) :
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ Tendsto (fun n => totalEnergy alpha (u (τ n)) -
        totalEnergy alpha (profileRemainder hDensity hSob P u J (τ n)) -
        ∑ j ∈ Finset.range J, totalEnergy alpha (profileAtom hDensity hSob P j (τ n)))
        atTop (𝓝 0) := by
    have hw (j : ℕ) (hj : j < J) : GradientWeakLimit (fun n =>
        (linearProfileFrame hDensity hSob (P.scale j n) (P.scale_pos j n)
          (P.center j n) (P.time j n)).symm (profileRemainder hDensity hSob P u j n))
        (P.profile j) := by
      apply profileRemainder_stage_weak
      apply hP.weak_remainder (j+1) j (Nat.lt_succ_self j)
      exact le_trans (by exact_mod_cast Nat.succ_le_of_lt hj) hJ
    obtain ⟨τ, hτ, he⟩ := finite_profile_energy_subsequence hDensity hRel hSob hfree hH hOrd
      (fun j => B + ∑ k ∈ Finset.range j, pureGradientNorm (P.profile k))
      P.scale P.scale_pos P.center P.time P.profile (profileRemainder hDensity hSob P u) J
      (fun j _ n => profileRemainder_succ hDensity hSob P u j n)
      (fun j _ n => profileRemainder_pureGradient_bound hDensity hSob P u hB j n) hw
    refine ⟨τ, hτ, ?_⟩
    simpa only [profileRemainder_zero, profileAtom] using he
  have halloc (J : ℕ) (hJ : (J : WithTop ℕ) ≤ P.count) :
      (∑ j ∈ Finset.range J, totalEnergy alpha (f j)) ≤ E0 := by
    obtain ⟨τ, hτ, hd⟩ := hsplit J hJ
    have hsum := tendsto_finsetSum (Finset.range J)
      (fun j _ => (hatom j).comp hτ.tendsto_atTop)
    have hr : Tendsto (fun n => totalEnergy alpha (profileRemainder hDensity hSob P u J (τ n)))
        atTop (𝓝 (E0 - ∑ j ∈ Finset.range J, totalEnergy alpha (f j))) := by
      convert ((hE.comp hτ.tendsto_atTop).sub hsum).sub hd using 1 <;> try simp only [sub_zero]
      funext n
      simp only [Function.comp_def]
      ring
    have hnon : 0 ≤ E0 - ∑ j ∈ Finset.range J, totalEnergy alpha (f j) := by
      apply ge_of_tendsto hr
      filter_upwards [hτ.tendsto_atTop.eventually ((hprefix J hJ).2)] with n hn
      have hc := state_kinetic_le_energy_below_W hOrd hH hS
        (profileRemainder hDensity hSob P u J (τ n)) hn.le
      have hg := gradientSquared_nonneg (profileRemainder hDensity hSob P u J (τ n))
      change gradientSquared _ ≤ kappa alpha * totalEnergy alpha _ at hc
      nlinarith
    linarith
  have hele (j : ℕ) : totalEnergy alpha (f j) ≤ E0 := by
    by_cases hj : (j : WithTop ℕ) < P.count
    · exact (Finset.single_le_sum (fun k _ => henon k)
        (Finset.mem_range.mpr (Nat.lt_succ_self j))).trans
        (halloc (j+1) (active_succ_eligible P j hj))
    · rw [hzero j (P.inactive_zero j hj)]
      exact hE0
  have hstable (j : ℕ) : ∃ t : ℝ,
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd (T j) (f j)
      t ∈ M.domain ∧ totalEnergy alpha (M.state t) = totalEnergy alpha (f j) ∧
      totalEnergy alpha (M.state t) < totalEnergy alpha (normalizedBubbleState alpha) ∧
      pureGradientNorm (M.state t) < pureGradientNorm (normalizedBubbleState alpha) := by
    have hg := (hmatch j).2.eventually (gt_mem_nhds ((hphi j).trans_lt hgap))
    obtain ⟨n, hn, hnG⟩ := ((hA j).1.and hg).exists
    have he := actualMaximalTrajectory_totalEnergy_constant hDensity hSob h0 hfree hret
      hefree heret hOrd S Bw Bs B6 (T j) (f j) (P.time j n) hn
    refine ⟨P.time j n, hn, he, ?_, ?_⟩
    · rw [he]
      exact (hele j).trans_lt hEW
    · exact (pureGradientNorm_lt_iff_gradientSquared_lt _ _).mpr hnG
  refine ⟨henon, hele, hco, hzero, hatom, (fun J hJ => (hprefix J hJ).1),
    (fun J hJ => (hprefix J hJ).2), hsplit, halloc, hstable, ?_⟩
  intro j t
  dsimp only
  intro htM
  obtain ⟨s, hs, he, hEW', hGW⟩ := hstable j
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd (T j) (f j)
  have hh := localMildTrajectory_sharp_W_trapping hDensity hSob h0 hfree hret hefree heret
    hOrd hH hS S Bw Bs B6 (M.recenter s hs) hEW' hGW t htM
  change gradientSquared (M.state t) ≤ kappa alpha * totalEnergy alpha (M.state s) ∧
    kappa alpha * totalEnergy alpha (M.state s) < gradientSquared (normalizedBubbleState alpha) at hh
  rw [he] at hh
  exact hh

end HartreeF.ActualProfileEnergy
