import FBackwardFixedPointDataComparison
import FTerminalCompactGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped Topology
namespace HartreeF.WaveCauchy
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalPathRestriction
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  freeCriticalPath backwardHartreeDuhamelMap criticalPathIntervalSource restrictPath

/-- Compose the previously proved actual small-cap comparison and late-error
properties. The final producer below discharges both properties from their
native Hartree theorems for one fixed baseline family. -/
theorem terminal_family_compact_cauchy (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha kernel B rho T S : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr) (hH : OrdinaryHLS alpha kernel)
    (hrho : 0 < rho) (phi : EnergyState)
    (hcompare : ∀ {a b : ℝ} (hab : a ≤ b) (f g : EnergyState)
      (u v : CriticalPath (intervalMeasure a b)),
      ‖energyPath _ u‖ ≤ B → ‖energyPath _ v‖ ≤ B →
      ‖fun j => criticalGradient _ j u‖ ≤ rho → ‖fun j => criticalGradient _ j v‖ ≤ rho →
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab f u = u →
      backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hab g v = v →
      ‖u-v‖ ≤ 2 * max (max (K^((6:ℝ)⁻¹)) 1 * Real.sqrt 3) Ch * ‖f-g‖)
    (U : ∀ R : ℝ, T ≤ R → CriticalPath (intervalMeasure T R))
    (hU : ∀ R (hTR : T ≤ R), backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH
      hTR (freeEnergyState hDensity hSob R phi) (U R hTR) = U R hTR)
    (hE : ∀ R (hTR : T ≤ R), ‖energyPath _ (U R hTR)‖ ≤ B)
    (hW : ∀ R (hTR : T ≤ R), ‖fun j => criticalGradient _ j (U R hTR)‖ ≤ rho)
    (hlate : ∀ delta : ℝ, 0 < delta → ∃ A : ℝ, ∃ hTA : T ≤ A,
      ∀ R (hAR : A ≤ R), ‖restrictPath hTA hAR le_rfl (U R (hTA.trans hAR)) -
        freeCriticalPath hDensity hSob hfree A R phi‖ ≤ delta/2)
    (hTS : T ≤ S) : CauchySeq (terminalCompactSequence hTS U) := by
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
  let lateChoice := hlate delta hdelta
  let A : ℝ := Classical.choose lateChoice
  let hTA : T ≤ A := Classical.choose (Classical.choose_spec lateChoice)
  have hlateR := Classical.choose_spec (Classical.choose_spec lateChoice)
  let natChoice := exists_nat_ge (A-T)
  let N : ℕ := Classical.choose natChoice
  have hN : A-T ≤ (N:ℝ) := Classical.choose_spec natChoice
  refine ⟨N,?_⟩
  intro n hn
  let R1 := max S (T+N)
  let R2 := max S (T+n)
  have hSR1 : S ≤ R1 := le_max_left _ _
  have hR1R2 : R1 ≤ R2 := max_le_max_left S (by
    have hcast : (N:ℝ)≤(n:ℝ) := Nat.cast_le.mpr hn
    linarith only [hcast])
  have hTR1 : T ≤ R1 := hTS.trans hSR1
  have hTR2 : T ≤ R2 := hTR1.trans hR1R2
  have hAR1 : A ≤ R1 := (show A ≤ T+N by linarith only [hN]).trans (le_max_right _ _)
  have hAR2 : A ≤ R2 := hAR1.trans hR1R2
  let u := U R1 hTR1
  let v := U R2 hTR2
  let w := restrictPath le_rfl hTR1 hR1R2 v
  let g := energyPath _ v ⟨R1,hTR1,hR1R2⟩
  have hw : backwardHartreeDuhamelMap hDensity hSob h0 hfree hret hH hTR1 g w = w :=
    restrictPath_backward_hartree_fixedPoint hDensity hSob h0 hfree hret hH
      le_rfl hTR1 hR1R2 (freeEnergyState hDensity hSob R2 phi) v (hU R2 hTR2)
  have hwE : ‖energyPath _ w‖ ≤ B :=
    (restrictPath_energy_norm_le le_rfl hTR1 hR1R2 v).trans (hE R2 hTR2)
  have hwW : ‖fun j => criticalGradient _ j w‖ ≤ rho := by
    apply (pi_norm_le_iff_of_nonneg hrho.le).mpr
    intro j
    exact (restrictPath_gradient_norm_le le_rfl hTR1 hR1R2 v j).trans
      ((norm_le_pi_norm (fun k => criticalGradient _ k v) j).trans (hW R2 hTR2))
  have hp : ‖g-freeEnergyState hDensity hSob R1 phi‖ ≤ delta/2 :=
    terminal_late_error_at hDensity hSob hfree hTA hAR2 hAR1 hR1R2 phi v (hlateR R2 hAR2)
  have hp' : ‖freeEnergyState hDensity hSob R1 phi-g‖ ≤ delta/2 :=
    (norm_sub_rev _ _).le.trans hp
  have hc : ‖u-w‖ ≤ 2*L*‖freeEnergyState hDensity hSob R1 phi-g‖ :=
    hcompare hTR1 (freeEnergyState hDensity hSob R1 phi) g u w
      (hE R1 hTR1) hwE (hW R1 hTR1) hwW (hU R1 hTR1) hw
  have hgap : ‖u-w‖ ≤ L*delta :=
    hc.trans ((mul_le_mul_of_nonneg_left hp' (by positivity)).trans_eq (by ring))
  have hs : ‖terminalCompactSequence hTS U N-terminalCompactSequence hTS U n‖ ≤ L*delta :=
    (nested_terminal_difference_bound hTS hSR1 hR1R2 u v).trans hgap
  calc
    dist (terminalCompactSequence hTS U n) (terminalCompactSequence hTS U N) =
        ‖terminalCompactSequence hTS U N-terminalCompactSequence hTS U n‖ := by
      exact (dist_eq_norm (terminalCompactSequence hTS U n)
        (terminalCompactSequence hTS U N)).trans (norm_sub_rev
          (terminalCompactSequence hTS U n) (terminalCompactSequence hTS U N))
    _ < epsilon := hs.trans_lt hsmall

end HartreeF.WaveCauchy
