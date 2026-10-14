import FR2GlobalXExhaustion

/-! Small profiles on the original canonical trajectory. The matching sequence
is consumed first for globality and then at every eventual index for fixed-LHS
limits. No small-profile X bound, correction estimate or globality is assumed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.R2Global
open EnergySpace CriticalPathSpace SobolevStretch StationarySelfTest TimeHolder
  CriticalTimeSobolev ProfileApproximation ProfileSpatialSmoothing
  HomogeneousStability IntervalNormExhaustion CriticalSourceBounds
  R2SmallData ActualStrichartz FreeDataDependence ActualDuhamelPath
  Retarded EndpointOutput ForcingDomain MaximalTrajectory
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] energySubmodule criticalPathSubmodule energyPath

/-- All three global domains and both real bounds are consequences of the
actual compact paths supplied by the local solver. -/
theorem anchored_global_bounds (hDensity : OrdinaryH1Density)
    {K Ch alpha a B D : ℝ} (hSob : OrdinarySobolev K)
    (hfree : OrdinaryHomogeneousStrichartz Ch) {f : EnergyState} {g : ℝ → EnergyState}
    (hg : Continuous g) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (h : AnchoredCompactBounds hDensity hSob hfree alpha a f g B D) :
    CurveFinite g ∧ xNorm g ≤ graphToXConstant K*B*‖f‖ ∧
      CurveFinite (g-anchoredFreeCurve hDensity hSob a f) ∧
      xNorm (g-anchoredFreeCurve hDensity hSob a f) ≤
        graphToXConstant K*D*‖f‖^(5+2*alpha) ∧
      (∀ t, pureGradientNorm (g t) ≤ Real.sqrt 3*B*‖f‖) := by
  obtain ⟨hfin,hx,hpoint⟩ := curveX_of_two_half_graph hDensity hSob g hg
    (mul_nonneg hB (norm_nonneg _)) (anchored_two_half_graph hDensity hSob hfree h)
  obtain ⟨hcfin,hcx,_⟩ := curveX_of_two_half_graph hDensity hSob
    (g-anchoredFreeCurve hDensity hSob a f)
    (hg.sub (anchoredFreeCurve_continuous hDensity hSob a f))
    (mul_nonneg hD (Real.rpow_nonneg (norm_nonneg _) _))
    (anchored_correction_two_half_graph hDensity hSob hfree h)
  refine ⟨hfin,?_,hcfin,?_,?_⟩
  · simpa only [mul_assoc] using xNorm_le
      (mul_nonneg (graphToXConstant_nonneg hSob) (mul_nonneg hB (norm_nonneg _))) hx
  · simpa only [mul_assoc] using xNorm_le
      (mul_nonneg (graphToXConstant_nonneg hSob)
        (mul_nonneg hD (Real.rpow_nonneg (norm_nonneg _) _))) hcx
  · intro t
    simpa only [mul_assoc] using hpoint t

/-- The mismatch term is a free orbit of the actual matching error. -/
theorem anchored_free_matching_difference (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (a : ℝ) (v phi : EnergyState) :
    anchoredFreeCurve hDensity hSob a v-anchoredFreeCurve hDensity hSob 0 phi =
      anchoredFreeCurve hDensity hSob a (v-freeEnergyState hDensity hSob a phi) := by
  funext t
  simp only [anchoredFreeCurve,Pi.sub_apply,sub_zero,freeEnergyState_sub]
  rw [← freeEnergyState_add_time,sub_add_cancel]

/-- Every retained nonlinear profile with sufficiently small pure-gradient
size is global on its own original canonical maximal trajectory. -/
theorem exists_same_canonical_small_profile_bounds (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha c : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha c) :
    ∃ delta Csd Ccorr : ℝ, 0 < delta ∧ 0 ≤ Csd ∧ 0 ≤ Ccorr ∧
      ∀ (T : ℝ) (f phi : EnergyState) (s : ℕ → ℝ),
        let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
        (∀ᶠ n in atTop, s n ∈ M.domain) →
        Tendsto (fun n => ‖M.state (s n)-freeEnergyState hDensity hSob (s n) phi‖)
          atTop (𝓝 0) →
        pureGradientNorm phi ≤ delta →
        M.domain = univ ∧ CurveFinite M.state ∧
          xNorm M.state ≤ Csd*pureGradientNorm phi ∧
          CurveFinite (M.state-anchoredFreeCurve hDensity hSob 0 phi) ∧
          xNorm (M.state-anchoredFreeCurve hDensity hSob 0 phi) ≤
            Ccorr*(pureGradientNorm phi)^(5+2*alpha) ∧
          (∀ t, pureGradientNorm (M.state t) ≤ Csd*pureGradientNorm phi) ∧
          (pureGradientNorm phi = 0 → ∀ t, M.state t = 0) := by
  obtain ⟨delta,B,D,hdelta,hB,hD,hcompact⟩ := exists_uniform_matching_compact_bounds
    hDensity hSob h0 hfree hret hefree heret hH
  let A := max (K^((6 : ℝ)⁻¹)) 1
  let G := graphToXConstant K
  let m := 5+2*alpha
  let Csd := (G+Real.sqrt 3)*B*A
  let Ccorr := G*D*A^m
  have hA : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  have hG : 0 ≤ G := graphToXConstant_nonneg hSob
  have hm : 0 < m := by dsimp [m]; linarith [hH.order_pos]
  have hCsd : 0 ≤ Csd := mul_nonneg (mul_nonneg (add_nonneg hG (Real.sqrt_nonneg _)) hB) hA
  have hCcorr : 0 ≤ Ccorr := mul_nonneg (mul_nonneg hG hD) (Real.rpow_nonneg hA _)
  refine ⟨delta,Csd,Ccorr,hdelta,hCsd,hCcorr,?_⟩
  intro T f phi s
  let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH T f
  intro hdom hmatch hsmall
  obtain ⟨hglobal,hpaths,hdata⟩ := hcompact T f phi s hdom hmatch hsmall
  have hcont : Continuous M.state := continuousOn_univ.mp (hglobal ▸ M.continuous)
  let a := pureGradientNorm phi
  let e := fun n => M.state (s n)-freeEnergyState hDensity hSob (s n) phi
  let b := fun n => A*a+‖e n‖
  have ha : 0 ≤ a := pureGradientNorm_nonneg phi
  have hb (n : ℕ) : 0 ≤ b n := add_nonneg (mul_nonneg hA ha) (norm_nonneg _)
  have hdat (n : ℕ) : ‖M.state (s n)‖ ≤ b n := hdata n
  have hlimb : Tendsto b atTop (𝓝 (A*a)) := by
    simpa only [b,add_zero] using tendsto_const_nhds.add hmatch
  have hlimpow : Tendsto (fun n => (b n)^m) atTop (𝓝 ((A*a)^m)) :=
    hlimb.rpow_const (Or.inr hm.le)
  obtain ⟨n0,hn0⟩ := hpaths.exists
  obtain ⟨hfin,_,_,_,_⟩ := anchored_global_bounds hDensity hSob hfree hcont hB hD hn0
  have hfreePhi := anchoredFreeCurve_bound hDensity hSob hfree 0 phi
  have hcorrfin : CurveFinite (M.state-anchoredFreeCurve hDensity hSob 0 phi) :=
    hfin.sub hfreePhi.1
  have hXevent : ∀ᶠ n in atTop, xNorm M.state ≤ G*B*b n := by
    filter_upwards [hpaths] with n hn
    have hx := (anchored_global_bounds hDensity hSob hfree hcont hB hD hn).2.1
    exact hx.trans (mul_le_mul_of_nonneg_left (hdat n) (mul_nonneg hG hB))
  have hXlim : xNorm M.state ≤ G*B*(A*a) :=
    ge_of_tendsto (hlimb.const_mul (G*B)) hXevent
  have hX : xNorm M.state ≤ Csd*a := by
    apply hXlim.trans
    dsimp [Csd]
    have h := mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 3) hB) hA) ha
    nlinarith
  have hPevent (t : ℝ) : ∀ᶠ n in atTop,
      pureGradientNorm (M.state t) ≤ Real.sqrt 3*B*b n := by
    filter_upwards [hpaths] with n hn
    have hp := (anchored_global_bounds hDensity hSob hfree hcont hB hD hn).2.2.2.2 t
    exact hp.trans (mul_le_mul_of_nonneg_left (hdat n)
      (mul_nonneg (Real.sqrt_nonneg _) hB))
  have hP (t : ℝ) : pureGradientNorm (M.state t) ≤ Csd*a := by
    have hp := ge_of_tendsto (hlimb.const_mul (Real.sqrt 3*B)) (hPevent t)
    apply hp.trans
    dsimp [Csd]
    have h := mul_nonneg (mul_nonneg (mul_nonneg hG hB) hA) ha
    nlinarith
  have hcorrevent : ∀ᶠ n in atTop,
      xNorm (M.state-anchoredFreeCurve hDensity hSob 0 phi) ≤
        G*D*(b n)^m+freeXConstant K Ch*Real.sqrt 3*‖e n‖ := by
    filter_upwards [hpaths] with n hn
    obtain ⟨_,_,hanch,hanchb,_⟩ := anchored_global_bounds hDensity hSob hfree hcont hB hD hn
    obtain ⟨herr,herrb⟩ := anchoredFreeCurve_bound hDensity hSob hfree (s n) (e n)
    have hid : M.state-anchoredFreeCurve hDensity hSob 0 phi =
        (M.state-anchoredFreeCurve hDensity hSob (s n) (M.state (s n)))+
          anchoredFreeCurve hDensity hSob (s n) (e n) := by
      rw [← anchored_free_matching_difference hDensity hSob (s n) (M.state (s n)) phi]
      abel
    rw [hid]
    apply (xNorm_add_le hanch herr).trans
    apply add_le_add
    · exact hanchb.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (hdat n) hm.le) (mul_nonneg hG hD))
    · exact herrb.trans ((mul_le_mul_of_nonneg_left (pureGradient_le_sqrt_three_energyState (e n))
        (freeXConstant_nonneg hSob hfree)).trans_eq (by ring))
  have hcorrlim : Tendsto (fun n => G*D*(b n)^m+
      freeXConstant K Ch*Real.sqrt 3*‖e n‖) atTop (𝓝 (G*D*(A*a)^m)) := by
    simpa only [mul_zero,add_zero] using
      (hlimpow.const_mul (G*D)).add (hmatch.const_mul (freeXConstant K Ch*Real.sqrt 3))
  have hcorr : xNorm (M.state-anchoredFreeCurve hDensity hSob 0 phi) ≤ Ccorr*a^m := by
    have hh := ge_of_tendsto hcorrlim hcorrevent
    exact hh.trans_eq (by rw [Real.mul_rpow hA ha]; dsimp [Ccorr]; ring)
  refine ⟨hglobal,hfin,hX,hcorrfin,hcorr,hP,?_⟩
  intro haz t
  apply (pureGradientNorm_eq_zero_iff hSob (M.state t)).mp
  exact le_antisymm (by simpa only [a,haz,mul_zero] using hP t) (pureGradientNorm_nonneg _)

end HartreeF.R2Global
