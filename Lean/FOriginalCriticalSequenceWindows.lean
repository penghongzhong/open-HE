import FOriginalUniformScatteringThreshold
import FActualBalancedGraphWindows

/-! Hartree v23 Lemma 2.16: finite-window replacement for the invalid
assumption that a past-halfline primitive is finite. All windows belong to
the actual native lifespan. This file does not assert the full lemma. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.OriginalCriticalWindows
open EnergySpace StateEnergy StateSharpThreshold MaximalTrajectory MaximalFiniteSGlobal
  SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
  SharpOrdinary Regularization.Actual HeatRiesz ActualCriticalThreshold
  OriginalUniformThreshold CriticalPathSpace CriticalSourceBounds CriticalPathRestriction

variable (hDensity : OrdinaryH1Density)
  {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
  (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
  (hret : OrdinaryRetardedStrichartz h0 Cr)
  (hefree : OrdinaryHomogeneousEndpointOutput Che)
  (heret : OrdinaryRetardedEndpointOutput h0 Cre)
  (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))

/-- Failure of a common sublevel bound yields a genuinely finite native window. -/
theorem exists_large_native_window {E T : ℝ}
    (hE : uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd < E)
    (hEW : E < totalEnergy alpha (normalizedBubbleState alpha)) :
    ∃ f : EnergyState, StableDatum alpha f ∧ totalEnergy alpha f ≤ E ∧
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
      ∃ (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ U.domain),
        ENNReal.ofReal T < pathValueSize (intervalMeasure a b) (U.path hab hI) := by
  obtain ⟨f, hf, he, hbad⟩ := exists_sublevel_datum_exceeding_bound
    hDensity hSob h0 hfree hret hefree heret hOrd hE hEW T.toNNReal
  refine ⟨f, hf, he, ?_⟩
  dsimp only
  by_contra hnot
  apply hbad
  intro a b hab hI
  exact le_of_not_gt (fun hlt => hnot ⟨a, b, hab, hI, hlt⟩)

/-- Both S norms exceed T at an interior point of one finite window.
No assumption is made on integrability over either infinite halfline. -/
theorem exists_balanced_native_window {E T : ℝ}
    (hE : uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd < E)
    (hEW : E < totalEnergy alpha (normalizedBubbleState alpha)) (hT : 0 < T) :
    ∃ f : EnergyState, StableDatum alpha f ∧ totalEnergy alpha f ≤ E ∧
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f
      ∃ (a b : ℝ) (hab : a ≤ b) (hI : Icc a b ⊆ U.domain)
        (c : ℝ) (hac : a < c) (hcb : c < b),
        ENNReal.ofReal T < pathValueSize (intervalMeasure a c)
          (restrictPath le_rfl hac.le hcb.le (U.path hab hI)) ∧
        ENNReal.ofReal T < pathValueSize (intervalMeasure c b)
          (restrictPath hac.le hcb.le le_rfl (U.path hab hI)) := by
  obtain ⟨f, hf, he, a, b, hab, hI, hlarge⟩ := exists_large_native_window
    hDensity hSob h0 hfree hret hefree heret hOrd (T := 2*T) hE hEW
  obtain ⟨c, hac, hcb, hleft, hright⟩ := BilateralWindows.exists_path_half_large_S
    hDensity hSob hab
      ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 f).path hab hI)
      hT hlarge
  exact ⟨f, hf, he, a, b, hab, hI, c, hac, hcb, hleft, hright⟩

/-- Diverging compact S bounds and ceilings converging to the uniform
threshold force the actual energies to converge to that SAME threshold. -/
theorem escaping_bounds_energy_tendsto
    (hne : (uniformEnergies hDensity hSob h0 hfree hret hefree heret hOrd).Nonempty)
    (u : ℕ → EnergyState) (ceiling : ℕ → ℝ)
    (hstable : ∀ n, StableDatum alpha (u n))
    (he : ∀ n, totalEnergy alpha (u n) ≤ ceiling n)
    (hceiling : Tendsto ceiling atTop
      (𝓝 (uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd)))
    (hescape : ∀ n, ¬ UniformCompactS
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd 0 (u n))
      (n : ℝ≥0)) :
    Tendsto (fun n => totalEnergy alpha (u n)) atTop
      (𝓝 (uniformCriticalLevel hDensity hSob h0 hfree hret hefree heret hOrd)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨R, hR⟩ := uniformSBelow_of_lt hDensity hSob h0 hfree hret hefree heret hOrd hne ha
    obtain ⟨N, hN⟩ := exists_nat_gt R
    filter_upwards [eventually_ge_atTop N] with n hn
    by_contra hnot
    have hen : totalEnergy alpha (u n) ≤ a := le_of_not_gt hnot
    have hRn : R ≤ (n : ℝ≥0) := hN.le.trans (by exact_mod_cast hn)
    apply hescape n
    intro l r hlr hI
    exact (hR (u n) (hstable n) hen l r hlr hI).trans (ENNReal.coe_le_coe.mpr hRn)
  · intro b hb
    filter_upwards [hceiling.eventually (gt_mem_nhds hb)] with n hn
    exact (he n).trans_lt hn

end HartreeF.OriginalCriticalWindows
