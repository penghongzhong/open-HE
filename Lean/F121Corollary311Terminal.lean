import FCompactFullZSFromSource
import FR2CompactSmallData
import FActualTwoSidedNormAssembly
import FActualTwoSidedFiniteSScattering
import FPositiveSmallEnergyScattering

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 200000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HartreeF.Paper121Corollary311
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest
open Retarded ActualStrichartz ForcingDomain ActualDuhamelPath CriticalUniqueness
open EndpointOutput FreeDataDependence CriticalSourceBounds IntervalTimeTransport
open MaximalTrajectory IntervalNormExhaustion ActualPerturbation CompactFullZS
open StateEnergy StateSharpThreshold Regularization.Actual SharpOrdinary HeatRiesz
open MaximalFiniteSGlobal DynamicSharpW
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath
  actualMaximalTrajectory freeEnergyState freeCriticalPath

/-- Original Corollary 3.11: all four literal norms, including the endpoint Z,
and the higher-order free correction belong to the same canonical solution.
Every source bound and scattering-size criterion is produced in the proof. -/
theorem corollary311_quantitative_small_data
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hH : OrdinaryHLS alpha kernel) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ 0 < C ∧
      ∀ (s : ℝ) (f : EnergyState), pureGradientNorm f ≤ epsilon →
      let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
      M.domain = Set.univ ∧
      actualPaperDifferenceSize Set.univ M.state (fun _ => (0 : EnergyState)) ≤
        ENNReal.ofReal (C*pureGradientNorm f) ∧
      actualPaperDifferenceSize Set.univ M.state
        (fun t => freeEnergyState hDensity hSob (t-s) f) ≤
        ENNReal.ofReal (C*(pureGradientNorm f)^(5+2*alpha)) ∧
      ∃ uMinus uPlus : EnergyState,
        Tendsto (fun t : ℝ => M.state t-freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
        Tendsto (fun t : ℝ => pureGradientNorm
          (M.state t-freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
        Tendsto (fun t : ℝ => M.state t-freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
        Tendsto (fun t : ℝ => pureGradientNorm
          (M.state t-freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) := by
  obtain ⟨delta,B,D,hdelta,hB,hD,hsolve⟩ := R2SmallData.exists_uniform_two_sided_small_data
    hDensity hSob h0 hfree hret hefree heret hH
  obtain ⟨Cs,hCs,hsrc⟩ := R2SmallData.exists_source_power_bound hDensity hSob hH
  let r : ℝ := 5+2*alpha
  have hr : 0 ≤ r := by dsimp [r]; linarith [hH.order_pos]
  have hr1 : 1 ≤ r := by dsimp [r]; linarith [hH.order_pos]
  let A0 : ℝ := max (K^((6:ℝ)⁻¹)) 1
  have hA0 : 0 ≤ A0 := zero_le_one.trans (le_max_right _ _)
  let eta : ℝ := min delta 1
  have heta : 0 < eta := lt_min hdelta zero_lt_one
  let epsilon : ℝ := eta/(A0+1)
  have hepsilon : 0 < epsilon := div_pos heta (by positivity)
  have hAepsilon : A0*epsilon ≤ eta := by
    dsimp only [epsilon]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < A0+1)).mpr
    nlinarith [heta.le]
  let N : ℝ := Cs*B^r
  have hN : 0 ≤ N := mul_nonneg hCs (Real.rpow_nonneg hB _)
  let L : ℝ := (1+scalarSConstant K+3*Che)*B+3*Cre*N
  let H : ℝ := (1+scalarSConstant K)*D+3*(Che*C0+Cre)*N
  have hS := scalarSConstant_nonneg hSob
  have hChe := hefree.1
  have hCre := heret.1
  have hC0 := h0.1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hHc : 0 ≤ H := by dsimp [H]; positivity
  let C : ℝ := 24*L*A0+24*H*A0^r+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨epsilon,C,hepsilon,hC,?_⟩
  intro s f hf
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH s f
  change M.domain = univ ∧ _
  have hneta : ‖f‖ ≤ eta := (energyState_le_pureGradient hSob f).trans
    ((mul_le_mul_of_nonneg_left hf hA0).trans hAepsilon)
  have hsmall : ‖f‖ ≤ delta := hneta.trans (min_le_left _ _)
  have hn1 : ‖f‖ ≤ 1 := hneta.trans (min_le_right _ _)
  have hnPower : ‖f‖^r ≤ ‖f‖ := Real.rpow_le_self_of_le_one (norm_nonneg f) hn1 hr1
  obtain ⟨hglobal,hb⟩ := hsolve s f hsmall
  have hdom : univ ⊆ M.domain := by rw [hglobal]
  have identify {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ M.domain)
      (p : CriticalPath (intervalMeasure a b))
      (hp : ∀ t : Icc a b, energyPath _ p t = M.state t) : p = M.path hab hI := by
    apply energyPath_injective (intervalMeasure a b)
    apply ContinuousMap.ext
    intro t
    exact (hp t).trans (M.path_agrees hab hI t).symm
  have forwardBounds (b : ℝ) (hsb : s ≤ b) (hI : Icc s b ⊆ M.domain) :
      ‖M.path hsb hI‖ ≤ B*‖f‖ ∧
      ‖M.path hsb hI-freeCriticalPath hDensity hSob hfree s b
        (freeEnergyState hDensity hSob (-s) f)‖ ≤ D*‖f‖^r := by
    obtain ⟨p,hp,hpN,hpD⟩ := hb.forward b hsb
    have he := identify hsb hI p hp
    rw [he] at hpN hpD
    exact ⟨hpN,hpD⟩
  have backwardBounds (a : ℝ) (has : a ≤ s) (hI : Icc a s ⊆ M.domain) :
      ‖M.path has hI‖ ≤ B*‖f‖ ∧
      ‖M.path has hI-freeCriticalPath hDensity hSob hfree a s
        (freeEnergyState hDensity hSob (-s) f)‖ ≤ D*‖f‖^r := by
    obtain ⟨p,hp,hpN,hpD⟩ := hb.backward a has
    have he := identify has hI p hp
    rw [he] at hpN hpD
    exact ⟨hpN,hpD⟩
  have hBN : 0 ≤ B*‖f‖ := mul_nonneg hB (norm_nonneg _)
  have hDN : 0 ≤ D*‖f‖^r := mul_nonneg hD (Real.rpow_nonneg (norm_nonneg _) _)
  have hNN : 0 ≤ N*‖f‖^r := mul_nonneg hN (Real.rpow_nonneg (norm_nonneg _) _)
  have sourceBound {a b : ℝ} (hab : a ≤ b) (u : CriticalPath (intervalMeasure a b))
      (hu : ‖u‖ ≤ B*‖f‖) :
      ‖(criticalPathIntervalSource hDensity hSob hH hab u 0).gradient‖ ≤ N*‖f‖^r := by
    have hs := (hsrc hab u).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg u) hu hr) hCs)
    apply hs.trans_eq
    rw [Real.mul_rpow hB (norm_nonneg f)]
    dsimp only [N]
    ring
  have fixedPoint {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ M.domain) :
      hartreeDuhamelMap hDensity hSob h0 hfree hret hH hab (M.state a) (M.path hab hI) =
        M.path hab hI :=
    (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH hab
      (M.state a) (M.path hab hI)).mp (M.path_mild hab hI)
  have totalBound {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ M.domain)
      (hu : ‖M.path hab hI‖ ≤ B*‖f‖) :
      fullZSDifferenceSize (M.path hab hI) 0 ≤ ENNReal.ofReal (L*‖f‖) := by
    have hh := forward_fullZS_of_graph_source hDensity hSob h0 hfree hret hefree heret hH
      hab (M.state a) (M.path hab hI) hBN hNN (fixedPoint hab hI) hu
      (sourceBound hab (M.path hab hI) hu)
    apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := mul_le_mul_of_nonneg_left hnPower (mul_nonneg (by positivity : 0 ≤ 3*Cre) hN)
    dsimp only [L]
    nlinarith only [hp]
  have rightCorrection (b : ℝ) (hsb : s ≤ b) (hI : Icc s b ⊆ M.domain) :
      fullZSDifferenceSize (M.path hsb hI)
        (freeCriticalPath hDensity hSob hfree s b (freeEnergyState hDensity hSob (-s) f)) ≤
        ENNReal.ofReal (H*‖f‖^r) := by
    have hfix := fixedPoint hsb hI
    rw [M.initial] at hfix
    have hu := forwardBounds b hsb hI
    have hh := forward_correction_fullZS_of_source hDensity hSob h0 hfree hret heret hH
      hsb f (M.path hsb hI) hDN hNN hfix hu.2 (sourceBound hsb (M.path hsb hI) hu.1)
    apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp only [H]
    have hx : 0 ≤ 3*(Che*C0)*(N*‖f‖^r) := by positivity
    nlinarith only [hx]
  have leftCorrection (a : ℝ) (has : a ≤ s) (hI : Icc a s ⊆ M.domain) :
      fullZSDifferenceSize (M.path has hI)
        (freeCriticalPath hDensity hSob hfree a s (freeEnergyState hDensity hSob (-s) f)) ≤
        ENNReal.ofReal (H*‖f‖^r) := by
    have ht : energyPath _ (M.path has hI) ⟨s,has,le_rfl⟩ = f :=
      (M.path_agrees has hI ⟨s,has,le_rfl⟩).trans M.initial
    have hback := forwardFixedPoint_is_backward_at_terminal
      hDensity hSob h0 hfree hret hH has (M.state a) (M.path has hI) (fixedPoint has hI)
    rw [ht] at hback
    have hu := backwardBounds a has hI
    have hh := backward_correction_fullZS_of_source hDensity hSob h0 hfree hret hefree heret hH
      has f (M.path has hI) hDN hNN hback hu.2 (sourceBound has (M.path has hI) hu.1)
    exact hh.trans_eq (congrArg ENNReal.ofReal (by dsimp only [H]; ring))
  let U : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ univ → CriticalPath (intervalMeasure a b) :=
    fun hab hsub => M.path hab (hsub.trans hdom)
  let Q0 : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ univ → CriticalPath (intervalMeasure a b) :=
    fun _ _ => 0
  let Qf : ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ univ → CriticalPath (intervalMeasure a b) :=
    fun {a b} _ _ => freeCriticalPath hDensity hSob hfree a b (freeEnergyState hDensity hSob (-s) f)
  have hU {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ univ) (t : Icc a b) :
      energyPath _ (U hab hsub) t = M.state t := M.path_agrees hab (hsub.trans hdom) t
  have hQ0 {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ univ) (t : Icc a b) :
      energyPath _ (Q0 hab hsub) t = (0 : EnergyState) := by
    change energyPath _ (0 : CriticalPath (intervalMeasure a b)) t = 0
    rw [map_zero, ContinuousMap.zero_apply]
  have hQf {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ univ) (t : Icc a b) :
      energyPath _ (Qf hab hsub) t = freeEnergyState hDensity hSob (t-s) f := by
    change energyPath _ (freeCriticalPath hDensity hSob hfree a b
      (freeEnergyState hDensity hSob (-s) f)) t = _
    rw [freeCriticalPath_energy, ← freeEnergyState_add_time, sub_eq_add_neg]
  have hLN : 0 ≤ L*‖f‖ := mul_nonneg hL (norm_nonneg _)
  have hHN : 0 ≤ H*‖f‖^r := mul_nonneg hHc (Real.rpow_nonneg (norm_nonneg _) _)
  have hreal := actualPaperRealization_of_anchored_compact_differences hDensity hSob hLN
    univ ordConnected_univ (mem_univ s) M.state (fun _ => 0) U Q0 hU hQ0
    (fun {a} _ has => totalBound has _ (backwardBounds a has _).1)
    (fun {b} _ hsb => totalBound hsb _ (forwardBounds b hsb _).1)
  have hrealDiff := actualPaperRealization_of_anchored_compact_differences hDensity hSob hHN
    univ ordConnected_univ (mem_univ s) M.state
    (fun t => freeEnergyState hDensity hSob (t-s) f) U Qf hU hQf
    (fun {a} _ has => leftCorrection a has _)
    (fun {b} _ hsb => rightCorrection b hsb _)
  have hfour := actualPaperDifferenceSize_le_of_realization (mul_nonneg (by norm_num) hLN) hreal
  have hfourDiff := actualPaperDifferenceSize_le_of_realization (mul_nonneg (by norm_num) hHN) hrealDiff
  have hnP : ‖f‖ ≤ A0*pureGradientNorm f := energyState_le_pureGradient hSob f
  have hpn : 0 ≤ pureGradientNorm f := pureGradientNorm_nonneg f
  have hpowP : ‖f‖^r ≤ A0^r*(pureGradientNorm f)^r :=
    (Real.rpow_le_rpow (norm_nonneg f) hnP hr).trans_eq (Real.mul_rpow hA0 hpn)
  have hlin : actualPaperDifferenceSize univ M.state (fun _ => 0) ≤
      ENNReal.ofReal (C*pureGradientNorm f) := by
    apply hfour.trans (ENNReal.ofReal_le_ofReal ?_)
    have hx := mul_le_mul_of_nonneg_left hnP (mul_nonneg (by norm_num : (0:ℝ) ≤ 24) hL)
    have hy : 0 ≤ (24*H*A0^r+1)*pureGradientNorm f := by positivity
    dsimp only [C]
    nlinarith only [hx,hy]
  have hcorrection : actualPaperDifferenceSize univ M.state
      (fun t => freeEnergyState hDensity hSob (t-s) f) ≤
      ENNReal.ofReal (C*(pureGradientNorm f)^r) := by
    apply hfourDiff.trans (ENNReal.ofReal_le_ofReal ?_)
    have hx := mul_le_mul_of_nonneg_left hpowP (mul_nonneg (by norm_num : (0:ℝ) ≤ 24) hHc)
    have hy : 0 ≤ (24*L*A0+1)*(pureGradientNorm f)^r := by positivity
    dsimp only [C]
    nlinarith only [hx,hy]
  let Msize : ℝ≥0 := Real.toNNReal (normComparisonConstant K*(B*‖f‖))
  have hplus : ActualScattering.FiniteSAfter M := by
    refine ⟨Msize,?_⟩
    intro b hsb hI
    have hp := (forwardBounds b hsb hI).1
    have hc : ‖fun j => criticalGradient (intervalMeasure s b) j (M.path hsb hI)‖ ≤ B*‖f‖ :=
      ((le_max_right _ _).trans_eq (criticalPath_norm _ (M.path hsb hI)).symm).trans hp
    exact (path_sizes_le_coordinate_cap (intervalMeasure s b) hDensity hSob hBN (M.path hsb hI) hc).2
  have hminus : ActualLeftScattering.FiniteSBefore M := by
    refine ⟨Msize,?_⟩
    intro a has hI
    have hp := (backwardBounds a has hI).1
    have hc : ‖fun j => criticalGradient (intervalMeasure a s) j (M.path has hI)‖ ≤ B*‖f‖ :=
      ((le_max_right _ _).trans_eq (criticalPath_norm _ (M.path has hI)).symm).trans hp
    exact (path_sizes_le_coordinate_cap (intervalMeasure a s) hDensity hSob hBN (M.path has hI) hc).2
  have hP (t : ℝ) : pureGradientNorm (M.state t) ≤ Real.sqrt 3*(B*‖f‖) :=
    (pureGradient_le_sqrt_three_energyState (M.state t)).trans
      (mul_le_mul_of_nonneg_left (R2SmallData.AnchoredCompactBounds.pointwise hDensity hSob hfree hb t)
        (Real.sqrt_nonneg _))
  obtain ⟨uMinus,uPlus,hm,hmp,hp,hpp⟩ :=
    ActualTwoSidedScattering.exists_actual_two_sided_scattering_of_finite_s
      hDensity hSob h0 hfree hret hH M hglobal hP hplus hminus
  exact ⟨hglobal,hlin,hcorrection,uMinus,uPlus,hm,hmp,hp,hpp⟩

/-- The final original stable-branch clause has a strictly positive universal
energy level, with the original two strict W thresholds. -/
theorem corollary311_positive_stable_energy_seed
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre)
    (hOrd : OrdinaryHLS alpha (standardRieszConstant alpha))
    (hH : SharpOrdinaryHLS alpha) (hS : SharpOrdinarySobolev)
    (S : OrdinaryBesselSmoothing) (Bw : OrdinaryBesselLp CriticalPathSpace.criticalExponent)
    (Bs : OrdinaryBesselLp Regularization.Actual.sourceExponent) (B6 : OrdinaryBesselLp 6) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ M : ℝ≥0, ∀ (s0 : ℝ) (u0 : EnergyState),
      totalEnergy alpha u0 < totalEnergy alpha (normalizedBubbleState alpha) →
      pureGradientNorm u0 < pureGradientNorm (normalizedBubbleState alpha) →
      totalEnergy alpha u0 ≤ epsilon →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hOrd s0 u0
      UniformCompactS U M ∧ U.domain = Set.univ ∧ ∃ uMinus uPlus : EnergyState,
        Tendsto (fun t : ℝ => U.state t-freeEnergyState hDensity hSob t uMinus) atBot (𝓝 0) ∧
        Tendsto (fun t : ℝ => pureGradientNorm
          (U.state t-freeEnergyState hDensity hSob t uMinus)) atBot (𝓝 0) ∧
        Tendsto (fun t : ℝ => U.state t-freeEnergyState hDensity hSob t uPlus) atTop (𝓝 0) ∧
        Tendsto (fun t : ℝ => pureGradientNorm
          (U.state t-freeEnergyState hDensity hSob t uPlus)) atTop (𝓝 0) :=
  SmallEnergy.exists_positive_small_energy_scattering
    hDensity hSob h0 hfree hret hefree heret hOrd hH hS S Bw Bs B6

end HartreeF.Paper121Corollary311
