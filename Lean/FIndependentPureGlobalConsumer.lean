import FActualGlobalIntervalStability
import FPaperNormCompactPerturbation
import FPaperNormBackwardCompactPerturbation

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace HartreeF.IndependentGlobalNormBridge
open EnergySpace CriticalPathSpace ActualDuhamelPath ActualPerturbation MaximalTrajectory
open CriticalSourceBounds SobolevStretch StationarySelfTest Retarded ActualStrichartz
open ForcingDomain CriticalUniqueness EndpointOutput HartreeDistributionalBridge LinearWeakEquation
open CompactLongTimePerturbation BackwardCompactLongTimePerturbation IntervalNormExhaustion
open HomogeneousStability IntervalPerturbation PaperNormCompactPerturbation TimeHolder
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath criticalGradient
  hartreeDuhamelMap backwardHartreeDuhamelMap criticalPathIntervalSource
  ActualNestedLpBound ActualPaperRealization actualPaperDifferenceSize fullZSDifferenceSize

/-- Independent pure-input consumer, composed directly from the anchored PDE
construction and actual norm exhaustion. The author global stability theorem is
imported for audit but is not invoked by this proof. Pointwise pure energy is
explicit; global source restriction and compact-path construction remain inputs.
The final constant is exactly 24*C_anchor*A, A=max(K^(1/6),1). -/
theorem exists_pure_input_global_stability (hDensity : OrdinaryH1Density)
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
      (∀ t ∈ I, pureGradientNorm (q t) ≤ B) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I),
        mixedNorm (intervalMeasure a b) volume 10 10
          (fun t => energyValue (energyPath _ (Q hab hI) t)) ≤ ENNReal.ofReal M) →
      (∀ {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ I), (E hab hI).paperForcingSize ≤ ENNReal.ofReal epsilon) →
      0 ≤ epsilon → epsilon ≤ epsilon0 → pureGradientNorm (f-q s) ≤ epsilon →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
      I ⊆ U.domain ∧
      ActualPaperRealization I (fun t => U.state t-q t) (C*epsilon) ∧
      actualPaperDifferenceSize I U.state q ≤ ENNReal.ofReal (C*epsilon) ∧
      ∀ t ∈ I, pureGradientNorm (U.state t-q t) ≤ C*epsilon := by
  let A : ℝ := max (K^((6 : ℝ)⁻¹)) 1
  have hA1 : 1 ≤ A := le_max_right _ _
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  let chosen := exists_actual_two_sided_interval_perturbation
    hDensity hSob h0 hfree hret hefree heret hH hgen hUnique
    (B := A*B) (M := M) (mul_nonneg hA.le hB) hM
  let epsilon0 : ℝ := Classical.choose chosen
  let constants := Classical.choose_spec chosen
  let C : ℝ := Classical.choose constants
  have hc := Classical.choose_spec constants
  have hC : 0 < C := hc.2.2.1
  refine ⟨epsilon0/A,(24*C)*A,div_pos hc.1 hA,
    (div_le_one hA).mpr (hc.2.1.trans hA1),
    mul_pos (mul_pos (by norm_num) hC) hA,?_⟩
  intro I hconn s epsilon hsI f q Q E hQ hPDE hE hS herr heps hsm hf
  have hsmall : A*epsilon ≤ epsilon0 := by
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hsm
  have hinit : ‖f-q s‖ ≤ A*epsilon := initial_graph_difference_le_of_pure hSob _ _ hf
  have henergy {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) :
      ‖energyPath _ (Q hab hsub)‖ ≤ A*B := by
    apply energyPath_norm_le_of_pure_cap hSob hB
    intro t
    rw [hQ hab hsub t]
    exact hE t (hsub t.property)
  have hscalar {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) :
      pathValueSize (intervalMeasure a b) (Q hab hsub) ≤ ENNReal.ofReal M :=
    (pathValueSize_eq_actual_S _).le.trans (hS hab hsub)
  have herror {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) :
      ‖(E hab hsub).gradient‖ ≤ A*epsilon :=
    ((E hab hsub).gradient_norm_le_of_paperForcingSize heps (herr hab hsub)).trans
      (le_mul_of_one_le_left heps hA1)
  have hmain := hc.2.2.2 I hconn hsI f q Q E hQ hPDE
    henergy hscalar herror (mul_nonneg hA.le heps) hsmall hinit
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  let paths : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ I → CriticalPath (intervalMeasure a b) :=
    fun hab hsub => U.path hab (hsub.trans hmain.1)
  have hpaths {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) (t : Icc a b) :
      energyPath _ (paths hab hsub) t=U.state t := U.path_agrees hab _ t
  have hl {a : ℝ} (ha : a ∈ I) (has : a ≤ s) :
      fullZSDifferenceSize (paths has (hconn.out' ha hsI)) (Q has (hconn.out' ha hsI)) ≤
        ENNReal.ofReal (C*(A*epsilon)) := by
    let solved := hmain.2.2.1 ha has
    let hU : Icc a s ⊆ U.domain := Classical.choose solved
    have hp := Classical.choose_spec solved
    exact hp.2.2.2.2.2.1
  have hr {b : ℝ} (hb : b ∈ I) (hsb : s ≤ b) :
      fullZSDifferenceSize (paths hsb (hconn.out' hsI hb)) (Q hsb (hconn.out' hsI hb)) ≤
        ENNReal.ofReal (C*(A*epsilon)) := by
    let solved := hmain.2.1 hb hsb
    let hU : Icc s b ⊆ U.domain := Classical.choose solved
    have hp := Classical.choose_spec solved
    exact hp.2.2.2.2.2.1
  have hCe : 0 ≤ C*(A*epsilon) := mul_nonneg hC.le (mul_nonneg hA.le heps)
  have hreal := actualPaperRealization_of_anchored_compact_differences hDensity hSob hCe
    I hconn hsI U.state q paths Q hpaths hQ hl hr
  have hbound := actualPaperDifferenceSize_le_of_realization (by positivity : 0 ≤ 6*(C*(A*epsilon))) hreal
  unfold ActualPaperRealization at hreal
  have h24 : 6*(C*(A*epsilon)) ≤ ((24*C)*A)*epsilon := by nlinarith only [hCe]
  have enlarge {X V : Type} [MeasurableSpace X] [NormedAddCommGroup V]
      (ν : Measure X) (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] (g : ℝ → X → V)
      (h : ActualNestedLpBound ν p r I g (6*(C*(A*epsilon)))) :
      ActualNestedLpBound ν p r I g (((24*C)*A)*epsilon) := by
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
  · exact hbound.trans_eq (congrArg ENNReal.ofReal (show 4*(6*(C*(A*epsilon)))=((24*C)*A)*epsilon from by ring))
  · intro t ht
    have hs3 : Real.sqrt 3 ≤ 24 := by
      apply (Real.sqrt_le_iff).mpr
      norm_num
    have hb := (pureGradient_le_sqrt_three_energyState (U.state t-q t)).trans
      (mul_le_mul_of_nonneg_left (hmain.2.2.2 t ht) (Real.sqrt_nonneg _))
    exact hb.trans ((mul_le_mul_of_nonneg_right hs3 hCe).trans_eq (by ring))

#print axioms exists_pure_input_global_stability
end HartreeF.IndependentGlobalNormBridge
