import FFreeCriticalFutureTail
import FFreeCriticalPastTail
import FUniformForwardInitialSolver
import FUniformBackwardTerminalSolver
import FBackwardFreePathDifference
import FClosedPerturbationMaximalIdentification
import FEnergyFreeConsumers

/-! Uniform half-line bounds for canonical trajectories whose marked data
converge to an actual free orbit at a diverging marked time. The energy cap
precedes the solver radius, the radius precedes the free tail, and all choices
precede every compact endpoint. This file is an UNCOMPILED proof draft. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.BilateralTail
open EnergySpace CriticalPathSpace ActualDuhamelPath IntervalTimeTransport
open SobolevStretch StationarySelfTest Retarded ActualStrichartz ForcingDomain
open CriticalUniqueness EndpointOutput MaximalTrajectory FreeDataDependence
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule
  freeCriticalPath energyPath criticalGradient freeEnergyState

/-- The triangle estimate for a continuous linear map, isolated from concrete graph types. -/
private theorem clm_norm_le_norm_sub_add {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [Module ℂ E] [Module ℂ F]
    (f : E →L[ℂ] F) (q p : E) : ‖f q‖ ≤ ‖f (q-p)‖+‖f p‖ := by
  have hcancel : (q-p)+p = q := sub_add_cancel q p
  have hmap : f ((q-p)+p) = f (q-p)+f p :=
    ContinuousLinearMap.map_add f (q-p) p
  have heq : f q = f (q-p)+f p :=
    (congrArg (fun x : E => f x) hcancel).symm.trans hmap
  calc
    ‖f q‖ = ‖f (q-p)+f p‖ := congrArg (fun y : F => ‖y‖) heq
    _ ≤ ‖f (q-p)‖+‖f p‖ := norm_add_le _ _

/-- A proposition-valued family has the same conclusion for every proof of its index. -/
private theorem forall_of_exists_proof (P : Prop) (Q : P → Prop)
    (hex : ∃ hP : P, Q hP) (hP : P) : Q hP :=
  Exists.elim hex (fun hP' hQ => (congrArg Q (proof_irrel hP' hP)).mp hQ)

/-- Divergence to positive time gives one bound for every future canonical
compact path and produces the entire actual future half-line. -/
theorem exists_eventual_future_graph_cap (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) (z : ℕ → EnergyState) (s : ℕ → ℝ)
    (hnorm : Tendsto (fun n => ‖z n-freeEnergyState hDensity hSob (s n) phi‖)
      atTop (𝓝 0)) (htime : Tendsto s atTop atTop) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        (s n) (z n)
      Ici (s n) ⊆ U.domain ∧
      ∀ (b : ℝ) (hb : s n ≤ b) (hI : Icc (s n) b ⊆ U.domain),
        ‖U.path hb hI‖ ≤ R := by
  let A : ℝ := max (K^((6:ℝ)⁻¹)) 1
  let CE : ℝ := A*Real.sqrt 3
  let Ephi : ℝ := A*pureGradientNorm phi
  have hA : 0 ≤ A := le_trans zero_le_one (le_max_right _ _)
  have hCE : 0 ≤ CE := mul_nonneg hA (Real.sqrt_nonneg _)
  have hEphi : 0 ≤ Ephi := mul_nonneg hA (pureGradientNorm_nonneg phi)
  let B : ℝ := 2*CE*(Ephi+1)+2
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨eta, heta, _heta1, hsolve⟩ :=
    WaveInitial.exists_uniform_forward_initial_radius hDensity hSob h0 hfree hret hH
      hB (by norm_num : (0:ℝ)<1)
  let Cf : ℝ := max CE Ch
  have hscaled : Tendsto (fun n => Cf*‖z n-freeEnergyState hDensity hSob (s n) phi‖)
      atTop (𝓝 0) := by simpa only [mul_zero] using hnorm.const_mul Cf
  obtain ⟨T,hT⟩ := WaveTerminal.exists_freeCriticalPath_future_small
    hDensity hSob hfree phi (show 0 < eta/4 by positivity)
  have hev : ∀ᶠ n in atTop,
      T ≤ s n ∧ ‖z n-freeEnergyState hDensity hSob (s n) phi‖ ≤ 1 ∧
      Cf*‖z n-freeEnergyState hDensity hSob (s n) phi‖ ≤ eta/4 := by
    filter_upwards [htime.eventually (eventually_ge_atTop T),
      hnorm.eventually (Iio_mem_nhds (show (0:ℝ)<1 by norm_num)),
      hscaled.eventually (Iio_mem_nhds (show 0<eta/4 by positivity))] with n hnt hne hns
    exact ⟨hnt,hne.le,hns.le⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨max B eta,hB.le.trans (le_max_left _ _),N,?_⟩
  intro n hn
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
    (s n) (z n)
  change Ici (s n) ⊆ U.domain ∧ _
  have hn' := hN n hn
  have hz : ‖z n‖ ≤ Ephi+1 := by
    have hw : ‖freeEnergyState hDensity hSob (s n) phi‖ ≤ Ephi := by
      simpa only [Ephi,A,freeEnergyState_pureGradientNorm] using
        energyState_le_pureGradient hSob (freeEnergyState hDensity hSob (s n) phi)
    calc
      ‖z n‖ = ‖(z n-freeEnergyState hDensity hSob (s n) phi)+
          freeEnergyState hDensity hSob (s n) phi‖ := by rw [sub_add_cancel]
      _ ≤ ‖z n-freeEnergyState hDensity hSob (s n) phi‖+
          ‖freeEnergyState hDensity hSob (s n) phi‖ := norm_add_le _ _
      _ ≤ Ephi+1 := by linarith [hn'.2.1]
  have hcompact (b : ℝ) (hb : s n ≤ b) :
      ∃ hI : Icc (s n) b ⊆ U.domain, ‖U.path hb hI‖ ≤ max B eta := by
    let q := freeCriticalPath hDensity hSob hfree (s n) b
      (freeEnergyState hDensity hSob (-(s n)) (z n))
    let p := freeCriticalPath hDensity hSob hfree (s n) b phi
    have hE : ‖energyPath _ q‖ ≤ B/2 := by
      have he := shiftedFreeCriticalPath_energy_norm_le hDensity hSob hfree
        (s n) b (z n)
      change ‖energyPath _ q‖ ≤ CE*‖z n‖ at he
      exact he.trans ((mul_le_mul_of_nonneg_left hz hCE).trans
        (by dsimp [B]; linarith))
    have hdiff : ‖q-p‖ ≤ eta/4 := by
      have hd := actual_shiftedFreeCriticalPath_difference_norm hDensity hSob hfree
        (s n) b (z n) (freeEnergyState hDensity hSob (s n) phi)
      have hd' : ‖q-p‖ ≤ Cf*‖z n-freeEnergyState hDensity hSob (s n) phi‖ := by
        simpa only [q,p,Cf,CE,A,freeEnergyState_left_inverse] using hd
      exact hd'.trans hn'.2.2
    have hW : ∀ j : Fin 3, ‖criticalGradient _ j q‖ ≤ eta/2 := by
      intro j
      have hp : ‖criticalGradient _ j p‖ ≤ eta/4 := hT (s n) b hn'.1 hb j
      have hd : ‖criticalGradient _ j (q-p)‖ ≤ eta/4 :=
        (criticalGradient_norm_le _ (q-p) j).trans hdiff
      calc
        ‖criticalGradient _ j q‖ ≤
            ‖criticalGradient _ j (q-p)‖+‖criticalGradient _ j p‖ :=
          clm_norm_le_norm_sub_add (criticalGradient (intervalMeasure (s n) b) j) q p
        _ ≤ eta/2 := by linarith only [hd, hp]
    obtain ⟨u,hfix,_htrace,huE,huW,_herr⟩ := hsolve hb (z n) hE hW
    have hmild := (isMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      hb (z n) u).mpr hfix
    obtain ⟨hI,hEq⟩ := actual_maximal_path_eq_of_closed_forward
      hDensity hSob h0 hfree hret hefree heret hH hb (z n) u hmild
    refine ⟨hI,?_⟩
    change ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
      (s n) (z n)).path hb hI‖ ≤ _
    have huNorm : ‖u‖ ≤ max B eta :=
      (criticalPath_norm (intervalMeasure (s n) b) u).le.trans (max_le_max huE huW)
    exact (congrArg (fun v : CriticalPath (intervalMeasure (s n) b) => ‖v‖)
      hEq).le.trans huNorm
  constructor
  · intro t ht
    obtain ⟨hI,_⟩ := hcompact t ht
    exact hI ⟨ht,le_rfl⟩
  · intro b hb hI
    exact forall_of_exists_proof (Icc (s n) b ⊆ U.domain)
      (fun hJ : Icc (s n) b ⊆ U.domain => ‖U.path hb hJ‖ ≤ max B eta)
      (hcompact b hb) hI

/-- Divergence to negative time gives one bound for every past canonical
compact path and produces the entire actual past half-line. -/
theorem exists_eventual_past_graph_cap (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (phi : EnergyState) (z : ℕ → EnergyState) (s : ℕ → ℝ)
    (hnorm : Tendsto (fun n => ‖z n-freeEnergyState hDensity hSob (s n) phi‖)
      atTop (𝓝 0)) (htime : Tendsto s atTop atBot) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
        (s n) (z n)
      Iic (s n) ⊆ U.domain ∧
      ∀ (a : ℝ) (ha : a ≤ s n) (hI : Icc a (s n) ⊆ U.domain),
        ‖U.path ha hI‖ ≤ R := by
  let A : ℝ := max (K^((6:ℝ)⁻¹)) 1
  let CE : ℝ := A*Real.sqrt 3
  let Ephi : ℝ := A*pureGradientNorm phi
  have hA : 0 ≤ A := le_trans zero_le_one (le_max_right _ _)
  have hCE : 0 ≤ CE := mul_nonneg hA (Real.sqrt_nonneg _)
  have hEphi : 0 ≤ Ephi := mul_nonneg hA (pureGradientNorm_nonneg phi)
  let B : ℝ := 2*CE*(Ephi+1)+2
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨eta, heta, _heta1, hsolve⟩ :=
    WaveTerminal.exists_uniform_backward_terminal_radius hDensity hSob h0 hfree hret hH
      hB (by norm_num : (0:ℝ)<1)
  let Cf : ℝ := max CE Ch
  have hscaled : Tendsto (fun n => Cf*‖z n-freeEnergyState hDensity hSob (s n) phi‖)
      atTop (𝓝 0) := by simpa only [mul_zero] using hnorm.const_mul Cf
  obtain ⟨T,hT⟩ := WaveInitial.exists_freeCriticalPath_past_small
    hDensity hSob hfree phi (show 0 < eta/4 by positivity)
  have hev : ∀ᶠ n in atTop,
      s n ≤ T ∧ ‖z n-freeEnergyState hDensity hSob (s n) phi‖ ≤ 1 ∧
      Cf*‖z n-freeEnergyState hDensity hSob (s n) phi‖ ≤ eta/4 := by
    filter_upwards [htime.eventually (eventually_le_atBot T),
      hnorm.eventually (Iio_mem_nhds (show (0:ℝ)<1 by norm_num)),
      hscaled.eventually (Iio_mem_nhds (show 0<eta/4 by positivity))] with n hnt hne hns
    exact ⟨hnt,hne.le,hns.le⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨max B eta,hB.le.trans (le_max_left _ _),N,?_⟩
  intro n hn
  let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
    (s n) (z n)
  change Iic (s n) ⊆ U.domain ∧ _
  have hn' := hN n hn
  have hz : ‖z n‖ ≤ Ephi+1 := by
    have hw : ‖freeEnergyState hDensity hSob (s n) phi‖ ≤ Ephi := by
      simpa only [Ephi,A,freeEnergyState_pureGradientNorm] using
        energyState_le_pureGradient hSob (freeEnergyState hDensity hSob (s n) phi)
    calc
      ‖z n‖ = ‖(z n-freeEnergyState hDensity hSob (s n) phi)+
          freeEnergyState hDensity hSob (s n) phi‖ := by rw [sub_add_cancel]
      _ ≤ ‖z n-freeEnergyState hDensity hSob (s n) phi‖+
          ‖freeEnergyState hDensity hSob (s n) phi‖ := norm_add_le _ _
      _ ≤ Ephi+1 := by linarith [hn'.2.1]
  have hcompact (a : ℝ) (ha : a ≤ s n) :
      ∃ hI : Icc a (s n) ⊆ U.domain, ‖U.path ha hI‖ ≤ max B eta := by
    let q := freeCriticalPath hDensity hSob hfree a (s n)
      (freeEnergyState hDensity hSob (-(s n)) (z n))
    let p := freeCriticalPath hDensity hSob hfree a (s n) phi
    have hE : ‖energyPath _ q‖ ≤ B/2 := by
      have he := BackwardUniformData.backwardFreeCriticalPath_energy_norm_le
        hDensity hSob hfree a (s n) (z n)
      change ‖energyPath _ q‖ ≤ CE*‖z n‖ at he
      exact he.trans ((mul_le_mul_of_nonneg_left hz hCE).trans
        (by dsimp [B]; linarith))
    have hdiff : ‖q-p‖ ≤ eta/4 := by
      have hd := BackwardUniformData.actual_backwardFreeCriticalPath_difference_norm
        hDensity hSob hfree a (s n) (z n) (freeEnergyState hDensity hSob (s n) phi)
      have hd' : ‖q-p‖ ≤ Cf*‖z n-freeEnergyState hDensity hSob (s n) phi‖ := by
        simpa only [q,p,Cf,CE,A,freeEnergyState_left_inverse] using hd
      exact hd'.trans hn'.2.2
    have hW : ∀ j : Fin 3, ‖criticalGradient _ j q‖ ≤ eta/2 := by
      intro j
      have hp : ‖criticalGradient _ j p‖ ≤ eta/4 := hT a (s n) hn'.1 ha j
      have hd : ‖criticalGradient _ j (q-p)‖ ≤ eta/4 :=
        (criticalGradient_norm_le _ (q-p) j).trans hdiff
      calc
        ‖criticalGradient _ j q‖ ≤
            ‖criticalGradient _ j (q-p)‖+‖criticalGradient _ j p‖ :=
          clm_norm_le_norm_sub_add (criticalGradient (intervalMeasure a (s n)) j) q p
        _ ≤ eta/2 := by linarith only [hd, hp]
    obtain ⟨u,hfix,_htrace,huE,huW,_herr⟩ := hsolve ha (z n) hE hW
    have hmild := (isBackwardMildHartreePath_iff_fixedPoint hDensity hSob h0 hfree hret hH
      ha (z n) u).mpr hfix
    obtain ⟨hI,hEq⟩ := actual_maximal_path_eq_of_closed_backward
      hDensity hSob h0 hfree hret hefree heret hH ha (z n) u hmild
    refine ⟨hI,?_⟩
    change ‖(actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH
      (s n) (z n)).path ha hI‖ ≤ _
    have huNorm : ‖u‖ ≤ max B eta :=
      (criticalPath_norm (intervalMeasure a (s n)) u).le.trans (max_le_max huE huW)
    exact (congrArg (fun v : CriticalPath (intervalMeasure a (s n)) => ‖v‖)
      hEq).le.trans huNorm
  constructor
  · intro t ht
    obtain ⟨hI,_⟩ := hcompact t ht
    exact hI ⟨le_rfl,ht⟩
  · intro a ha hI
    exact forall_of_exists_proof (Icc a (s n) ⊆ U.domain)
      (fun hJ : Icc a (s n) ⊆ U.domain => ‖U.path ha hJ‖ ≤ max B eta)
      (hcompact a ha) hI

#print axioms exists_eventual_future_graph_cap
#print axioms exists_eventual_past_graph_cap
end HartreeF.BilateralTail
