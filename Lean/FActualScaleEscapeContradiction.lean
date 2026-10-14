import FActualCompactTimeConvergence
import FActualBilateralPathTools
import FL6GaugeRelativeBounds
import FCriticalAffineL2Continuity

/-! The strong-limit contradiction in the subparabolic-scale argument.
Intrinsic L6 gauges rule out a nonzero strong limit of a fixed datum at
diverging spatial scales. Actual affine covariance identifies the return time.
The final subparabolic ratio estimate is not asserted by this module. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualScaleEscape
open EnergySpace CriticalAffine L6OrbitGauge MaximalTrajectory MaximalAffine AffineMixed
open SobolevStretch StationarySelfTest Retarded ActualStrichartz EndpointOutput ForcingDomain
open LinearWeakEquation BilateralPathTools ActualCompactTimeConvergence
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
attribute [local irreducible] energySubmodule actualMaximalTrajectory

/-- A fixed nonzero state cannot have a nonzero strong limit after normalization
at scales tending to infinity, regardless of the centers. -/
theorem normalized_scale_atTop_not_nonzero_limit
    (f : EnergyState) (hf : f ≠ 0) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (y : ℕ → Space) (hscale : Tendsto r atTop atTop)
    (g : EnergyState) (hg : g ≠ 0)
    (hlim : Tendsto (fun n => (criticalAffineState (r n) (hr n) (y n)).symm f)
      atTop (𝓝 g)) : False := by
  obtain ⟨R, x, hGauge⟩ := exists_gauge hf
  let v (n : ℕ) := (criticalAffineState (r n) (hr n) (y n)).symm f
  have hv (n : ℕ) : Gauge (v n) (R / r n) ((r n)⁻¹ • (x - y n)) := by
    apply gauge_criticalAffine_pullback (hr n) (y n)
    simpa only [v, (criticalAffineState (r n) (hr n) (y n)).apply_symm_apply] using hGauge
  obtain ⟨a, ha, _S, _hS, hbound⟩ := relative_parameter_bounds hlim hg hv
  have hzero : Tendsto (fun n => R / r n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Pi.inv_apply, mul_zero] using hscale.inv_tendsto_atTop.const_mul R
  obtain ⟨n, hn, hnsmall⟩ := (hbound.and (hzero.eventually (Iio_mem_nhds ha))).exists
  exact (not_lt_of_ge hn.1) hnsmall

/-- At normalized time -c/r², the normalized actual trajectory returns to
the normalized original datum. Domain membership is proved as well. -/
theorem actual_normalized_return_time
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (f : EnergyState) (c : ℝ)
    (hc : c ∈ (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain)
    {r : ℝ} (hr : 0 < r) (y : Space) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f
    let z := (criticalAffineState r hr y).symm (M.state c)
    let U := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 z
    (-c / r^2) ∈ U.domain ∧ U.state (-c / r^2) = (criticalAffineState r hr y).symm f := by
  intro M z U
  let N := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH c (M.state c)
  have hNM := actualMaximalTrajectory_recenter hDensity hSob h0 hfree hret hefree heret hH f hc
  let covarianceAt : ℝ → EnergyState → Prop := fun mark datum =>
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH mark datum
    V.domain = (timeAffine r c) ⁻¹' N.domain ∧
      EqOn V.state (fun t => affineState hr y (N.state (timeAffine r c t))) V.domain
  have hraw : covarianceAt ((c - c) / r^2) (affineState hr y (M.state c)) :=
    actualMaximalTrajectory_affine hDensity hSob h0 hfree hret hefree heret hH
      hr y c c (M.state c)
  have hmark : (c - c) / r^2 = 0 := by simp only [sub_self, zero_div]
  have hdatum : affineState hr y (M.state c) = z :=
    (criticalAffineState_symm_eq_affineState _ _ _ _).symm
  have hcov : covarianceAt 0 z := Eq.mp (congrArg₂ covarianceAt hmark hdatum) hraw
  have htime : timeAffine r c (-c / r^2) = 0 := by
    unfold timeAffine
    field_simp [hr.ne'] <;> ring
  have hNzero : (0 : ℝ) ∈ N.domain := by
    rw [hNM.1]
    exact M.center_mem
  have hmem : -c / r^2 ∈ U.domain := by
    rw [hcov.1]
    change timeAffine r c (-c / r^2) ∈ N.domain
    rw [htime]
    exact hNzero
  refine ⟨hmem, ?_⟩
  have he : U.state (-c / r^2) =
      affineState hr y (N.state (timeAffine r c (-c / r^2))) := hcov.2 hmem
  rw [htime] at he
  exact (he.trans (congrArg (affineState hr y)
    ((hNM.2 M.center_mem).trans M.initial))).trans
      (criticalAffineState_symm_eq_affineState _ _ _ _).symm

/-- A global reference solution permits every convergent moving time sequence.
No uniform global spacetime norm is assumed. -/
theorem moving_time_tendsto_of_global
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (psi : EnergyState) (z : ℕ → EnergyState)
    (hz : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0))
    (hglobal :
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).domain = univ)
    (tau : ℕ → ℝ) (t : ℝ) (htau : Tendsto tau atTop (𝓝 t)) :
    Tendsto (fun n =>
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 (z n)).state
        (tau n)) atTop
      (𝓝 ((actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).state t)) := by
  let a := min 0 (t - 1)
  let b := max 0 (t + 1)
  have ha : a < t := (min_le_right _ _).trans_lt (by linarith)
  have hb : t < b := (show t < t + 1 by linarith).trans_le (le_max_right _ _)
  have hI : Icc a b ⊆
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi).domain := by
    rw [hglobal]
    exact subset_univ _
  have htauI : ∀ᶠ n in atTop, tau n ∈ Icc a b := by
    filter_upwards [htau.eventually (Ioi_mem_nhds ha), htau.eventually (Iio_mem_nhds hb)] with n hn hn'
    exact ⟨hn.le, hn'.le⟩
  exact (actual_moving_time_tendsto hDensity hSob h0 hfree hret hefree heret hH
    hgen hUnique psi z hz (min_le_left _ _) (le_max_left _ _) tau htau
      ⟨ha.le, hb.le⟩ htauI hI).2

/-- Under a global nonzero strong limit of normalized data, an escaping
spatial scale forces the return times to have no finite limit. -/
theorem normalized_return_time_not_tendsto
    (hDensity : OrdinaryH1Density)
    {K C0 Ch Cr Che Cre alpha kernel : ℝ} (hSob : OrdinarySobolev K)
    (h0 : OrdinaryEndpointBound C0) (hfree : OrdinaryHomogeneousStrichartz Ch)
    (hret : OrdinaryRetardedStrichartz h0 Cr)
    (hefree : OrdinaryHomogeneousEndpointOutput Che)
    (heret : OrdinaryRetardedEndpointOutput h0 Cre) (hH : OrdinaryHLS alpha kernel)
    (hgen : OrdinaryFreeDistributionScalarGenerator)
    (hUnique : OrdinaryL2CompactHomogeneousUniqueness)
    (f : EnergyState) (hf : f ≠ 0) (c r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (y : ℕ → Space)
    (hc : ∀ n, c n ∈
      (actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f).domain)
    (hscale : Tendsto r atTop atTop) (psi : EnergyState) :
    let M := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 f
    let z := fun n => (criticalAffineState (r n) (hr n) (y n)).symm (M.state (c n))
    let V := actualMaximalTrajectory hDensity hSob h0 hfree hret hefree heret hH 0 psi
    Tendsto z atTop (𝓝 psi) → V.domain = univ → (∀ t, V.state t ≠ 0) →
      ∀ t : ℝ, ¬ Tendsto (fun n => -c n / (r n)^2) atTop (𝓝 t) := by
  intro M z V hz hglobal hnonzero t ht
  have hzNorm : Tendsto (fun n => ‖z n - psi‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hz.sub (tendsto_const_nhds (x := psi))).norm
  have heval := moving_time_tendsto_of_global hDensity hSob h0 hfree hret hefree heret hH
    hgen hUnique psi z hzNorm hglobal (fun n => -c n / (r n)^2) t ht
  have hnormalized : Tendsto
      (fun n => (criticalAffineState (r n) (hr n) (y n)).symm f) atTop (𝓝 (V.state t)) :=
    heval.congr' (Eventually.of_forall fun n =>
      (actual_normalized_return_time hDensity hSob h0 hfree hret hefree heret hH
        f (c n) (hc n) (hr n) (y n)).2)
  exact normalized_scale_atTop_not_nonzero_limit f hf r hr y hscale
    (V.state t) (hnonzero t) hnormalized

end HartreeF.ActualScaleEscape

