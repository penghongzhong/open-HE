import FActualTwoSidedIntervalPerturbation
import FActualTwoSidedNormAssembly

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IntervalPerturbation
open EnergySpace CriticalPathSpace ActualDuhamelPath ActualPerturbation MaximalTrajectory
open CriticalSourceBounds SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
open CompactLongTimePerturbation BackwardCompactLongTimePerturbation IntervalNormExhaustion
open HomogeneousStability
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  hartreeDuhamelMap backwardHartreeDuhamelMap criticalPathIntervalSource
  ActualNestedLpBound ActualPaperRealization actualPaperDifferenceSize fullZSDifferenceSize

/-- Genuine long-time stability on every connected real interval. The actual
maximal solution covers I; all four global mixed-Lp representatives and the
literal paper sum are outputs. The constant includes the factor24 from the two
half-interval exhaustion/Euclidean norm assembly. Input graph-energy and datum
bounds, local critical paths and compatible L1 sources remain explicit. -/
theorem exists_actual_global_interval_stability (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel B M : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che) (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ epsilon0 C : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 ∧ 0 < C ∧
      ∀ (I : Set ℝ) (_hconn : OrdConnected I) {s epsilon : ℝ} (_hsI : s ∈ I),
      ∀ (f : EnergyState) (q : ℝ → EnergyState)
      (Q : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CriticalPath (intervalMeasure a b))
      (E : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CompatibleL1IntervalSource a b),
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I) (t : Icc a b),
        energyPath _ (Q hab hI) t = q t) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I),
        ForcedHartreeCompactTestIdentity alpha kernel hab (Q hab hI) (E hab hI)) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I), ‖energyPath _ (Q hab hI)‖ ≤ B) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I),
        pathValueSize (intervalMeasure a b) (Q hab hI) ≤ ENNReal.ofReal M) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I), ‖(E hab hI).gradient‖ ≤ epsilon) →
      0 ≤ epsilon → epsilon ≤ epsilon0 → ‖f-q s‖ ≤ epsilon →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
      I ⊆ U.domain ∧
      ActualPaperRealization I (fun t => U.state t-q t) (C*epsilon) ∧
      actualPaperDifferenceSize I U.state q ≤ ENNReal.ofReal (C*epsilon) ∧
      ∀ t ∈ I, pureGradientNorm (U.state t-q t) ≤ C*epsilon := by
  let chosen := exists_actual_two_sided_interval_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique hB hM
  let epsilon0 : ℝ := Classical.choose chosen
  let constants := Classical.choose_spec chosen
  let C : ℝ := Classical.choose constants
  have hc := Classical.choose_spec constants
  have hC : 0 < C := hc.2.2.1
  refine ⟨epsilon0,24*C,hc.1,hc.2.1,mul_pos (by norm_num) hC,?_⟩
  intro I hconn s epsilon hsI f q Q E hQ hPDE hE hS herr heps hsm hf
  have hmain := hc.2.2.2 I hconn hsI f q Q E hQ hPDE hE hS herr heps hsm hf
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  let paths : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CriticalPath (intervalMeasure a b) :=
    fun hab hsub => U.path hab (hsub.trans hmain.1)
  have hpaths {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) (t : Icc a b) :
      energyPath _ (paths hab hsub) t=U.state t := U.path_agrees hab _ t
  have hl {a : ℝ} (ha : a ∈ I) (has : a ≤ s) :
      fullZSDifferenceSize (paths has (hconn.out' ha hsI)) (Q has (hconn.out' ha hsI)) ≤
        ENNReal.ofReal (C*epsilon) := by
    let solved := hmain.2.2.1 ha has
    let hU : Icc a s ⊆ U.domain := Classical.choose solved
    have hp := Classical.choose_spec solved
    exact hp.2.2.2.2.2.1
  have hr {b : ℝ} (hb : b ∈ I) (hsb : s ≤ b) :
      fullZSDifferenceSize (paths hsb (hconn.out' hsI hb)) (Q hsb (hconn.out' hsI hb)) ≤
        ENNReal.ofReal (C*epsilon) := by
    let solved := hmain.2.1 hb hsb
    let hU : Icc s b ⊆ U.domain := Classical.choose solved
    have hp := Classical.choose_spec solved
    exact hp.2.2.2.2.2.1
  have hCe : 0 ≤ C*epsilon := mul_nonneg hC.le heps
  have hreal := actualPaperRealization_of_anchored_compact_differences hDensity hSob hCe
    I hconn hsI U.state q paths Q hpaths hQ hl hr
  have hbound := actualPaperDifferenceSize_le_of_realization (by positivity : 0 ≤ 6*(C*epsilon)) hreal
  unfold ActualPaperRealization at hreal
  have h24 : 6*(C*epsilon) ≤ (24*C)*epsilon := by nlinarith only [hCe]
  have enlarge {X V : Type} [MeasurableSpace X] [NormedAddCommGroup V]
      (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] (g : ℝ → X → V)
      (h : ActualNestedLpBound ν p r I g (6*(C*epsilon))) :
      ActualNestedLpBound ν p r I g ((24*C)*epsilon) := by
    unfold ActualNestedLpBound at h ⊢
    obtain ⟨F,hF,ha,hz⟩ := h
    exact ⟨F,hF.trans h24,ha,hz⟩
  let : Fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩
  refine ⟨hmain.1,?_,?_,?_⟩
  · unfold ActualPaperRealization
    exact ⟨enlarge volume ∞ 2 _ hreal.1,
      enlarge volume 10 criticalExponent _ hreal.2.1,
      enlarge volume 2 6 _ hreal.2.2.1,
      enlarge volume 10 10 _ hreal.2.2.2⟩
  · exact hbound.trans_eq (congrArg ENNReal.ofReal (show 4*(6*(C*epsilon))=(24*C)*epsilon from by ring))
  · intro t ht
    have hs3 : Real.sqrt 3 ≤ 24 := by
      apply (Real.sqrt_le_iff).mpr
      norm_num
    have hb := (pureGradient_le_sqrt_three_energyState (U.state t-q t)).trans
      (mul_le_mul_of_nonneg_left (hmain.2.2.2 t ht) (Real.sqrt_nonneg _))
    exact hb.trans ((mul_le_mul_of_nonneg_right hs3 hCe).trans_eq (by ring))

#print axioms exists_actual_global_interval_stability
end HartreeF.IntervalPerturbation
