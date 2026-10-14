import FForwardFixedPointDataComparison
import FInitialCompactGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveInitialCauchy
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  freeCriticalPath hartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- The actual small-cap comparison and early-error properties imply compact
Cauchy convergence of one fixed initial family. The final producer discharges
these intermediate properties from native Hartree theorems. -/
theorem initial_family_compact_cauchy (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B rho T S : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hrho : 0 < rho) (phi : EnergyState)
    (hcompare : ∀ {a b : ℝ} (hab : a ≤ b) (f g : EnergyState)
      (u v : CriticalPath (intervalMeasure a b)),
      ‖energyPath _ u‖ ≤ B → ‖energyPath _ v‖ ≤ B →
      ‖fun j => criticalGradient _ j u‖ ≤ rho → ‖fun j => criticalGradient _ j v‖ ≤ rho →
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u = u →
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g v = v →
      ‖u-v‖ ≤ 2 * max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖)
    (U : ∀ R : ℝ, R ≤ T → CriticalPath (intervalMeasure R T))
    (hU : ∀ R (hRT : R ≤ T), hartreeDuhamelMap hDensity hSob h0 hfree hret hH
      hRT (freeEnergyState hDensity hSob R phi) (U R hRT) = U R hRT)
    (hE : ∀ R (hRT : R ≤ T), ‖energyPath _ (U R hRT)‖ ≤ B)
    (hW : ∀ R (hRT : R ≤ T), ‖fun j => criticalGradient _ j (U R hRT)‖ ≤ rho)
    (hearly : ∀ delta : ℝ, 0 < delta → ∃ A : ℝ, ∃ hAT : A ≤ T,
      ∀ R (hRA : R ≤ A), ‖restrictPath le_rfl hRA hAT (U R (hRA.trans hAT)) -
        freeCriticalPath hDensity hSob hfree R A phi‖ ≤ delta/2)
    (hST : S ≤ T) : CauchySeq (initialCompactSequence hST U) := by
  apply Metric.cauchySeq_iff'.mpr
  intro epsilon hepsilon
  let L := max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch
  have hL : 0 ≤ L := hfree.1.trans (le_max_right _ _)
  let delta := epsilon/(2*(L+1))
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hidentity : (L+1)*delta=epsilon/2 := by
    dsimp [delta]
    field_simp
  have hscale : L*delta ≤ (L+1)*delta :=
    mul_le_mul_of_nonneg_right (by linarith) hdelta.le
  have hsmall : L*delta < epsilon :=
    (hscale.trans_eq hidentity).trans_lt (half_lt_self hepsilon)
  let earlyChoice := hearly delta hdelta
  let A : ℝ := Classical.choose earlyChoice
  let hAT : A ≤ T := Classical.choose (Classical.choose_spec earlyChoice)
  have hearlyR := Classical.choose_spec (Classical.choose_spec earlyChoice)
  let natChoice := exists_nat_ge (T-A)
  let N : ℕ := Classical.choose natChoice
  have hN : T-A ≤ (N:ℝ) := Classical.choose_spec natChoice
  refine ⟨N,?_⟩
  intro n hn
  let R1 := min S (T-N)
  let R2 := min S (T-n)
  have hR1S : R1 ≤ S := min_le_left _ _
  have hR2R1 : R2 ≤ R1 := min_le_min_left S (by
    have hcast : (N:ℝ)≤(n:ℝ) := Nat.cast_le.mpr hn
    linarith only [hcast])
  have hR1T : R1 ≤ T := hR1S.trans hST
  have hR2T : R2 ≤ T := hR2R1.trans hR1T
  have hR1A : R1 ≤ A := (min_le_right _ _).trans (show T-N ≤ A by linarith only [hN])
  have hR2A : R2 ≤ A := hR2R1.trans hR1A
  let u := U R1 hR1T
  let v := U R2 hR2T
  let w := restrictPath hR2R1 hR1T le_rfl v
  let g := energyPath _ v ⟨R1,hR2R1,hR1T⟩
  have hw : hartreeDuhamelMap hDensity hSob h0 hfree hret hH hR1T g w = w :=
    restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
      hR2R1 hR1T le_rfl (freeEnergyState hDensity hSob R2 phi) v (hU R2 hR2T)
  have hwE : ‖energyPath _ w‖ ≤ B :=
    (restrictPath_energy_norm_le hR2R1 hR1T le_rfl v).trans (hE R2 hR2T)
  have hwW : ‖fun j => criticalGradient _ j w‖ ≤ rho := by
    apply (pi_norm_le_iff_of_nonneg hrho.le).mpr
    intro j
    exact (restrictPath_gradient_norm_le hR2R1 hR1T le_rfl v j).trans
      ((norm_le_pi_norm (fun k => criticalGradient _ k v) j).trans (hW R2 hR2T))
  have hp : ‖g-freeEnergyState hDensity hSob R1 phi‖ ≤ delta/2 :=
    initial_early_error_at hDensity hSob hfree hAT hR2A hR2R1 hR1A phi v (hearlyR R2 hR2A)
  have hp' : ‖freeEnergyState hDensity hSob R1 phi-g‖ ≤ delta/2 :=
    (norm_sub_rev _ _).le.trans hp
  have hc : ‖u-w‖ ≤ 2*L*‖freeEnergyState hDensity hSob R1 phi-g‖ :=
    hcompare hR1T (freeEnergyState hDensity hSob R1 phi) g u w
      (hE R1 hR1T) hwE (hW R1 hR1T) hwW (hU R1 hR1T) hw
  have hgap : ‖u-w‖ ≤ L*delta :=
    hc.trans ((mul_le_mul_of_nonneg_left hp' (by positivity)).trans_eq (by ring))
  have hs : ‖initialCompactSequence hST U N-initialCompactSequence hST U n‖ ≤ L*delta :=
    (nested_initial_difference_bound hST hR1S hR2R1 u v).trans hgap
  calc
    dist (initialCompactSequence hST U n) (initialCompactSequence hST U N) =
        ‖initialCompactSequence hST U N-initialCompactSequence hST U n‖ := by
      exact (dist_eq_norm (initialCompactSequence hST U n)
        (initialCompactSequence hST U N)).trans (norm_sub_rev
          (initialCompactSequence hST U n) (initialCompactSequence hST U N))
    _ < epsilon := hs.trans_lt hsmall

end HartreeF.WaveInitialCauchy
