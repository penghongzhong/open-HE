import FMaximalFiniteSGlobalScattering
import FSmallSGraphBound
import FActualSPartition
import FPartitionGlobalGraphBound
import FHartreeSubintervalFixedPoint
import FR2GlobalXExhaustion
import FActualResidualCompactSource
import FActualDynamicSharpWTrapping

/-! Actual finite S and the same canonical global finite-X curve.
The graph bound is built on literal compact paths by a single small-S radius,
the actual quantitative partition, rebased mildness and whole-graph assembly.
The reverse direction uses nested AE representatives and the established
subtype-to-real-time compact norm transport. Static author source; UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.FiniteSActualX
open EnergySpace CriticalPathSpace IntervalTimeTransport CriticalSourceBounds
  CriticalJointSources CriticalPathRestriction CriticalUniqueness ActualDuhamelPath
  MaximalTrajectory MaximalFiniteSGlobal SobolevStretch StationarySelfTest
  Retarded ActualStrichartz EndpointOutput ForcingDomain ActualPathPartitions
  R2Global StateEnergy EnergyVariation StateSharpThreshold Regularization.Actual
  SharpOrdinary HeatRiesz BubbleProfile TimeHolder
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  hartreeDuhamelMap jointFields

/-- Uniform actual finite S and a native state cap give one bound for every
actual compact graph. The real partition count is kept without rounding. -/
theorem uniform_compact_graph_of_finiteS (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr alpha c s0 B : ℝ} {u0 : EnergyState}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (hfree : OrdinaryHomogeneousStrichartz Ch) (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hH : OrdinaryHLS alpha c) (U : LocalMildTrajectory alpha c s0 u0)
    (hstate : ∀ t ∈ U.domain, ‖U.state t‖ ≤ B)
    (hfiniteS : FiniteSOnDomain U) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (a b : ℝ) (hab : a ≤ b)
      (hI : Set.Icc a b ⊆ U.domain), ‖U.path hab hI‖ ≤ R := by
  have hB : 0 ≤ B := (norm_nonneg (U.state s0)).trans (hstate s0 U.center_mem)
  obtain ⟨M, hM⟩ := hfiniteS
  obtain ⟨eta, heta, _, hsmall⟩ :=
    SmallSGraphBound.exists_small_s_energy_coordinate_graph_bound
      hDensity hSob h0 hfree hret hH hB
  let C : ℝ := max (max (K ^ ((6 : ℝ)⁻¹)) 1 * Real.sqrt 3) Ch
  have hC : 0 ≤ C :=
    (mul_nonneg (le_trans zero_le_one (le_max_right _ _)) (Real.sqrt_nonneg 3)).trans
      (le_max_left _ _)
  let H : ℝ := 2*C*B
  have hHnonneg : 0 ≤ H := mul_nonneg (mul_nonneg (by norm_num) hC) hB
  let N : ℝ := (M : ℝ) ^ (10 : ℕ) / eta ^ (10 : ℕ) + 1
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨N*H, mul_nonneg hN hHnonneg, ?_⟩
  intro a b hab hI
  let q := U.path hab hI
  obtain ⟨P, hcount, hpieces⟩ := exists_actual_small_S_partition hDensity hSob hab q heta
  have hqS : (pathValueSize (intervalMeasure a b) q).toReal ≤ (M : ℝ) := by
    simpa only [ENNReal.coe_toReal] using
      ENNReal.toReal_mono ENNReal.coe_ne_top (hM a b hab hI)
  have hcountN : (P.count : ℝ) ≤ N := by
    apply hcount.trans
    exact add_le_add
      (div_le_div_of_nonneg_right
        (pow_le_pow_left₀ ENNReal.toReal_nonneg hqS 10) (pow_nonneg heta.le 10)) le_rfl
  have hagrees (i : Fin P.count)
      (t : Set.Icc (P.time i.castSucc) (P.time i.succ)) :
      energyPath _ (piecePath P q i) t = U.state t := by
    exact (FinitePerturbation.piecePath_energy P q i t).trans
      (U.path_agrees hab hI
        ⟨t, (P.mem_interval i.castSucc).1.trans t.property.1,
          t.property.2.trans (P.mem_interval i.succ).2⟩)
  have hpieceNorm (i : Fin P.count) : ‖piecePath P q i‖ ≤ H := by
    have hpI : Set.Icc (P.time i.castSucc) (P.time i.succ) ⊆ U.domain := by
      intro t ht
      exact hI ⟨(P.mem_interval i.castSucc).1.trans ht.1,
        ht.2.trans (P.mem_interval i.succ).2⟩
    have hpE : ‖energyPath _ (piecePath P q i)‖ ≤ B := by
      apply (ContinuousMap.norm_le _ hB).mpr
      intro t
      rw [hagrees i t]
      exact hstate t (hpI t.property)
    have hpdatum : ‖U.state (P.time i.castSucc)‖ ≤ B :=
      hstate _ (hI (P.mem_interval i.castSucc))
    have hfix := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      hab (U.state a) q).mp (U.path_mild hab hI)
    have hrestrict := restrictPath_hartree_fixedPoint hDensity hSob h0 hfree hret hH
      (P.mem_interval i.castSucc).1 (piece_order P i) (P.mem_interval i.succ).2
      (U.state a) q hfix
    have hpmild : IsMildHartreePath (piece_order P i) alpha c
        (U.state (P.time i.castSucc)) (piecePath P q i) := by
      apply (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
        (piece_order P i) (U.state (P.time i.castSucc)) (piecePath P q i)).mpr
      simpa only [piecePath, q, U.path_agrees] using hrestrict
    exact (hsmall (piece_order P i) (U.state (P.time i.castSucc))
      (piecePath P q i) hpmild hpE (hpieces i)).trans
        (mul_le_mul_of_nonneg_left hpdatum (mul_nonneg (by norm_num) hC))
  exact (FinitePerturbation.global_graph_norm_le_piece_bound hab P q hHnonneg hpieceNorm).trans
    (mul_le_mul_of_nonneg_right hcountN hHnonneg)

/-- The public generic canonical forward bridge. Its pure-gradient cap is
explicit; maximality is the definition of the very same canonical trajectory. -/
theorem actualMaximalTrajectory_global_curveFinite_of_finiteS
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c G : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c)
    (s0 : ℝ) (u0 : EnergyState)
    (hgradient : ∀ t ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0).domain,
      pureGradientNorm
        ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0).state t) ≤ G)
    (hfiniteS : FiniteSOnDomain
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0)) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
    U.domain = Set.univ ∧ CurveFinite U.state := by
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s0 u0
  have hglobal : U.domain = Set.univ := maximal_domain_eq_univ_of_finite_s
    hDensity hSob h0 hfree hret hefree heret hH u0 U rfl hgradient hfiniteS
  have hstate : ∀ t ∈ U.domain, ‖U.state t‖ ≤ max (K ^ ((6 : ℝ)⁻¹)) 1 * G :=
    state_cap_of_pure_gradient hSob U hgradient
  obtain ⟨R, hR, hgraph⟩ := uniform_compact_graph_of_finiteS
    hDensity hSob h0 hfree hret hH U hstate hfiniteS
  have hcontinuous : Continuous U.state := by
    exact continuousOn_univ.mp (hglobal ▸ U.continuous)
  have htwo : TwoHalfGraphBound U.state s0 R := by
    constructor
    · intro b hbs
      have hI : Set.Icc b s0 ⊆ U.domain := by rw [hglobal]; exact Set.subset_univ _
      exact ⟨U.path hbs hI, U.path_agrees hbs hI, hgraph b s0 hbs hI⟩
    · intro b hsb
      have hI : Set.Icc s0 b ⊆ U.domain := by rw [hglobal]; exact Set.subset_univ _
      exact ⟨U.path hsb hI, U.path_agrees hsb hI, hgraph s0 b hsb hI⟩
  exact ⟨hglobal, (curveX_of_two_half_graph hDensity hSob U.state hcontinuous hR htwo).1⟩

/-- Nested AE equality identifies the actual S size of a compact path with
its canonical energy-value representatives. No pointwise quotient claim. -/
theorem actual_path_value_size {a b : ℝ} (q : CriticalPath (intervalMeasure a b)) :
    pathValueSize (intervalMeasure a b) q =
      mixedNorm (intervalMeasure a b) volume 10 10
        (fun t => energyValue (energyPath _ q t)) := by
  exact mixedNorm_congr_slices (intervalMeasure a b) 10 10
    ((jointFields (intervalMeasure a b) q).slice_eq.mono fun _ ht => ht.1)

/-- Reverse bridge on the same actual curve. Compact interval transport is
provided by curveCompactPath_value_mixed_le, including singleton intervals. -/
theorem finiteS_of_global_curveFinite {alpha c s0 : ℝ} {u0 : EnergyState}
    (U : LocalMildTrajectory alpha c s0 u0) (hglobal : U.domain = Set.univ)
    (hX : CurveFinite U.state) : FiniteSOnDomain U := by
  let M : ℝ≥0 := ⟨(curveS U.state).toReal, ENNReal.toReal_nonneg⟩
  have hM : (M : ℝ≥0∞) = curveS U.state := by
    calc
      (M : ℝ≥0∞) = ENNReal.ofReal (M : ℝ) := ENNReal.coe_nnreal_eq M
      _ = curveS U.state := ENNReal.ofReal_toReal hX.value
  refine ⟨M, ?_⟩
  intro a b hab hI
  have hIall : Set.Icc a b ⊆ U.domain := by rw [hglobal]; exact Set.subset_univ _
  have heq : U.path hab hIall = FullResidual.curveCompactPath hX hab := by
    apply energyPath_injective (intervalMeasure a b)
    apply ContinuousMap.ext
    intro t
    exact (U.path_agrees hab hIall t).trans
      (FullResidual.curveCompactPath_energy hX hab t).symm
  have hbound : pathValueSize (intervalMeasure a b) (U.path hab hIall) ≤ (M : ℝ≥0∞) := by
    rw [heq, actual_path_value_size, hM]
    exact FullResidual.curveCompactPath_value_mixed_le hX hab
  calc
    pathValueSize (intervalMeasure a b) (U.path hab hI) =
        pathValueSize (intervalMeasure a b) (U.path hab hIall) := rfl
    _ ≤ (M : ℝ≥0∞) := hbound

/-- On the original stable W branch, true native conservation and trapping
produce the cap. Finite S is the only additional trajectory-size hypothesis. -/
theorem actualMaximalTrajectory_stable_global_curveFinite_of_finiteS
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp criticalExponent)
    (Bs : OrdinaryBesselLp sourceExponent) (B6 : OrdinaryBesselLp 6)
    (s0 : ℝ) (u0 : EnergyState)
    (henergy : totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha))
    (hgradient : pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha))
    (hfiniteS : FiniteSOnDomain
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0)) :
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
    U.domain = Set.univ ∧ CurveFinite U.state := by
  have hcap := DynamicSharpW.actualMaximalTrajectory_pureGradient_cap
    hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6
      s0 u0 henergy hgradient
  exact actualMaximalTrajectory_global_curveFinite_of_finiteS
    hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
      (fun t ht => (hcap t ht).1) hfiniteS

end HartreeF.FiniteSActualX
