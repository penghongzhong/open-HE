import FActualEuclideanForcingNorm
import FActualBackwardCompactLongTimePerturbation

/-! Positive terminal-data compact-interval perturbation with the literal homogeneous
paper inputs. Ordinary analytic interfaces remain hypotheses. The scalar
Hartree forcing is the existing p = 3 + alpha forcing, with 0 < alpha < 3
contained in OrdinaryHLS. No mass or variance premise is added. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.PaperNormCompactPerturbation
open EnergySpace CriticalPathSpace ActualDuhamelPath ActualPerturbation
open BackwardCompactLongTimePerturbation CriticalSourceBounds
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
open HomogeneousStability EssentialEnergyCap TimeHolder
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  CriticalJointSources.jointFields fullZSDifferenceSize paperZSDifferenceSize
  ForcedHartreeCompactTestIdentity IsMildHartreePath IsBackwardMildHartreePath FullZPath
  energyComplexGradient pureGradientNorm pathValueSize mixedNorm
  CompatibleL1IntervalSource.paperForcingSize

/-- A uniform epsilon threshold and paper-output constant for every positive
closed interval. The only quantitative path inputs are the actual essential
Euclidean gradient energy, the original scalar S norm, the pure terminal
dotH1 discrepancy, and the same source's Euclidean N norm. -/
theorem exists_paper_norm_uniform_backward_compact_perturbation (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < C ∧
      ∀ {a b epsilon : ℝ} (hab : a < b) (f : EnergyState)
      (q : CriticalPath (intervalMeasure a b)) (E : CompatibleL1IntervalSource a b),
      ForcedHartreeCompactTestIdentity alpha kernel hab.le q E →
      mixedNorm (intervalMeasure a b) volume ∞ 2
        (fun t => energyComplexGradient (energyPath _ q t)) ≤ ENNReal.ofReal B →
      mixedNorm (intervalMeasure a b) volume 10 10
        (fun t => energyValue (energyPath _ q t)) ≤ ENNReal.ofReal M →
      0 ≤ epsilon → epsilon ≤ epsilon0 →
      pureGradientNorm (f-energyPath _ q ⟨b,hab.le,le_rfl⟩) ≤ epsilon →
      E.paperForcingSize ≤ ENNReal.ofReal epsilon →
      ∃ u : CriticalPath (intervalMeasure a b),
        IsBackwardMildHartreePath hab.le alpha kernel f u ∧ FullZPath u ∧ FullZPath (u-q) ∧
        energyPath _ u ⟨b,hab.le,le_rfl⟩ = f ∧
        (∀ t, pureGradientNorm (energyPath _ (u-q) t) ≤ C*epsilon) ∧
        paperZSDifferenceSize u q ≤ ENNReal.ofReal (C*epsilon) ∧
        ∀ v : CriticalPath (intervalMeasure a b),
          IsBackwardMildHartreePath hab.le alpha kernel f v → v=u := by
  let A : ℝ := max (K^((6 : ℝ)⁻¹)) 1
  have hA1 : 1 ≤ A := le_max_right _ _
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  let result := exists_actual_uniform_backward_compact_perturbation hDensity hSob h0 hfree hret
    hefree heret hH hgen hUnique (B := A*B) (M := M) (mul_nonneg hA.le hB) hM
  let delta : ℝ := Classical.choose result
  let rest := Classical.choose_spec result
  let Cg : ℝ := Classical.choose rest
  have hs0 := Classical.choose_spec rest
  have hd : 0 < delta := hs0.1
  have hd1 : delta ≤ 1 := hs0.2.1
  have hCg : 0 < Cg := hs0.2.2.1
  have hCA : 0 < Cg*A := mul_pos hCg hA
  have hs : 0 < Real.sqrt 3+4 := by positivity
  refine ⟨delta/A, (Real.sqrt 3+4)*(Cg*A), div_pos hd hA,
    (div_le_one hA).mpr (hd1.trans hA1), mul_pos hs hCA, ?_⟩
  intro a b epsilon hab f q E hPDE hE hS heps hepsSmall hf herr
  have hsmall : A*epsilon ≤ delta := by
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hepsSmall
  have hinit : ‖f-energyPath _ q ⟨b,hab.le,le_rfl⟩‖ ≤ A*epsilon :=
    initial_graph_difference_le_of_pure hSob _ _ hf
  have herror : ‖E.gradient‖ ≤ A*epsilon :=
    (E.gradient_norm_le_of_paperForcingSize heps herr).trans
      (le_mul_of_one_le_left heps hA1)
  have henergy : ‖energyPath _ q‖ ≤ A*B :=
    energyPath_norm_le_of_actual_energy_cap hSob hab hB q hE
  have hscalar : pathValueSize (intervalMeasure a b) q ≤ ENNReal.ofReal M :=
    (pathValueSize_eq_actual_S q).le.trans hS
  let solved := hs0.2.2.2 hab.le f q E hPDE
    henergy hscalar (mul_nonneg hA.le heps) hsmall hinit herror
  let u : CriticalPath (intervalMeasure a b) := Classical.choose solved
  have hu0 := Classical.choose_spec solved
  have hfull := hu0.2.2.2.2.2.1
  have hfull' : fullZSDifferenceSize u q ≤ ENNReal.ofReal ((Cg*A)*epsilon) := by
    simpa only [mul_assoc] using hfull
  have hout := paper_stability_bounds_of_fullZS u q hCA.le heps hfull'
  refine ⟨u,hu0.1,hu0.2.1,hu0.2.2.1,hu0.2.2.2.1,?_,hout.2,hu0.2.2.2.2.2.2⟩
  intro t
  exact (hout.1 t).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 4)) hCA.le) heps)

#print axioms exists_paper_norm_uniform_backward_compact_perturbation
end HartreeF.PaperNormCompactPerturbation
