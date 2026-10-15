import FNativeCompactFiniteEndpointGlobal

/-! R8.4 Proposition 5.4 with the compact-closure hypothesis itself.
Neither a mass bound nor regularity of the pointwise parameters is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.Paper121CompactGlobal
open EnergySpace SobolevStretch StationarySelfTest Retarded ActualStrichartz
  EndpointOutput ForcingDomain MaximalTrajectory CriticalAffine LinearWeakEquation
  NativeCompactGlobal

theorem no_finite_endpoint_of_compact_closure (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel s : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hOrd : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (f : EnergyState) (hf : f ≠ 0) (r : ℝ → ℝ) (y : ℝ → Space) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s f
    ∀ hr : ∀ t ∈ U.domain, 0 < r t,
      IsCompact (closure {q : EnergyState | ∃ (t : ℝ) (ht : t ∈ U.domain),
        q = (criticalAffineState (r t) (hr t ht) (y t)).symm (U.state t)}) →
      ¬ BddAbove U.domain ∧ ¬ BddBelow U.domain ∧ U.domain = univ := by
  intro U hr hc
  have hmem : ∀ t (ht : t ∈ U.domain),
      (criticalAffineState (r t) (hr t ht) (y t)).symm (U.state t) ∈
        closure {q : EnergyState | ∃ (z : ℝ) (hz : z ∈ U.domain),
          q = (criticalAffineState (r z) (hr z hz) (y z)).symm (U.state z)} := by
    intro t ht
    exact subset_closure ⟨t, ht, rfl⟩
  obtain ⟨hu, hl⟩ := actual_compact_normalized_domain_unbounded
    hDensity hSob h0 hfree hret hefree heret hOrd hgen f hf hc r y hr hmem
  exact ⟨hu, hl, actual_compact_normalized_global
    hDensity hSob h0 hfree hret hefree heret hOrd hgen f hf hc r y hr hmem⟩

end HartreeF.Paper121CompactGlobal
