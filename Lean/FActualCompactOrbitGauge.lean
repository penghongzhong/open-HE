import FCriticalAffineL2Continuity
import FL6GaugeRelativeBounds
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A fixed mass gauge converts actual spatial sequential concentration to one
compact closure in the original EnergyState. No continuity of the chosen gauge
is used or asserted. Author source; UNCOMPILED. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace HartreeF.ActualCompactOrbitGauge
open EnergySpace SobolevStretch CriticalAffine L6OrbitGauge

/-- The compactness premise used privately by the assembly is supplied by the
actual native-window/Palais--Smale producer at the public orbit entry. -/
def SpatialSequentialConcentration {ι : Type*} (u : ι → EnergyState) : Prop :=
  ∀ t : ℕ → ι,
    ∃ (k : ℕ → ℕ) (lambda : ℕ → ℝ) (hlambda : ∀ n, 0 < lambda n)
      (y : ℕ → Space) (v : EnergyState),
      StrictMono k ∧
      Tendsto (fun n => (criticalAffineState (lambda n) (hlambda n) (y n)).symm
        (u (t (k n)))) atTop (𝓝 v) ∧ v ≠ 0

private theorem fixed_gauge_subsequence {K : ℝ} (hSob : OrdinarySobolev K)
    {ι : Type*} (u : ι → EnergyState)
    (hseq : SpatialSequentialConcentration u)
    (r : ι → ℝ) (y : ι → Space) (hg : ∀ i, Gauge (u i) (r i) (y i))
    (t : ℕ → ι) :
    ∃ (k : ℕ → ℕ), StrictMono k ∧ ∃ w : EnergyState,
      Tendsto (fun n => (criticalAffineState (r (t (k n)))
        (hg (t (k n))).radius_pos (y (t (k n)))).symm (u (t (k n))))
        atTop (𝓝 w) := by
  classical
  obtain ⟨k, lambda, hlambda, z, vLim, hk, hv, hvLimNe⟩ := hseq t
  let v (n : ℕ) := (criticalAffineState (lambda n) (hlambda n) (z n)).symm
    (u (t (k n)))
  let rho (n : ℕ) := r (t (k n)) / lambda n
  let c (n : ℕ) := (lambda n)⁻¹ • (y (t (k n)) - z n)
  have hvlim : Tendsto v atTop (𝓝 vLim) := hv
  have hback (n : ℕ) : criticalAffineState (lambda n) (hlambda n) (z n) (v n) =
      u (t (k n)) :=
    (criticalAffineState (lambda n) (hlambda n) (z n)).apply_symm_apply _
  have hgr (n : ℕ) : Gauge (v n) (rho n) (c n) := by
    apply gauge_criticalAffine_pullback (hlambda n) (z n)
    rw [hback]
    exact hg (t (k n))
  obtain ⟨r0, hr0, S, _hS, hbounded⟩ := relative_parameter_bounds hvlim hvLimNe hgr
  have hparamCompact : IsCompact (Icc r0 (2*S) ×ˢ Metric.closedBall (0 : Space) (3*S)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hevent : ∀ᶠ n in atTop,
      (rho n, c n) ∈ Icc r0 (2*S) ×ˢ Metric.closedBall (0 : Space) (3*S) := by
    filter_upwards [hbounded] with n hn
    exact ⟨⟨hn.1, hn.2.1⟩, by simpa only [Metric.mem_closedBall, dist_zero_right] using hn.2.2⟩
  obtain ⟨p, hp, tau, htau, hparam⟩ := hparamCompact.tendsto_subseq' hevent.frequently
  have hp0 : 0 < p.1 := hr0.trans_le hp.1.1
  have hrlim : Tendsto (fun n => rho (tau n)) atTop (𝓝 p.1) := hparam.fst_nhds
  have hclim : Tendsto (fun n => c (tau n)) atTop (𝓝 p.2) := hparam.snd_nhds
  have hvl : Tendsto (fun n => v (tau n)) atTop (𝓝 vLim) :=
    hvlim.comp htau.tendsto_atTop
  have hlimit := affineState_tendsto_data hSob
    (fun n => rho (tau n)) (fun n => (hgr (tau n)).radius_pos)
    (fun n => c (tau n)) hp0 hrlim hclim (fun n => v (tau n)) hvl
  have hidentity (n : ℕ) :
      (criticalAffineState (r (t (k (tau n)))) (hg (t (k (tau n)))).radius_pos
        (y (t (k (tau n))))).symm (u (t (k (tau n)))) =
      affineState (hgr (tau n)).radius_pos (c (tau n)) (v (tau n)) := by
    exact (congrArg
      (fun w : EnergyState =>
        (criticalAffineState (r (t (k (tau n))))
          (hg (t (k (tau n)))).radius_pos (y (t (k (tau n))))).symm w)
      (hback (tau n)).symm).trans
        (criticalAffineState_symm_apply_relative _ _
          (hg (t (k (tau n)))).radius_pos (hlambda (tau n)) _ _ _)
  refine ⟨k ∘ tau, hk.comp htau, affineState hp0 p.2 vLim, ?_⟩
  exact hlimit.congr' (Eventually.of_forall fun n => (hidentity n).symm)

/-- A genuine compact closure of one fixed choice of normalized states.
The choice functions themselves have no asserted regularity. -/
theorem exists_compact_normalization {K : ℝ} (hSob : OrdinarySobolev K)
    {ι : Type*} (u : ι → EnergyState) (hne : ∀ i, u i ≠ 0)
    (hseq : SpatialSequentialConcentration u) :
    ∃ (r : ι → ℝ) (hr : ∀ i, 0 < r i) (y : ι → Space),
      IsCompact (closure (range (fun i => (criticalAffineState (r i) (hr i) (y i)).symm (u i)))) := by
  classical
  choose r y hg using fun i => exists_gauge (hne i)
  let hr (i : ι) : 0 < r i := (hg i).radius_pos
  let p (i : ι) := (criticalAffineState (r i) (hr i) (y i)).symm (u i)
  have hpseq (t : ℕ → ι) : ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ w : EnergyState,
      Tendsto (fun n => p (t (k n))) atTop (𝓝 w) :=
    fixed_gauge_subsequence hSob u hseq r y hg t
  refine ⟨r, hr, y, IsSeqCompact.isCompact ?_⟩
  intro w hw
  have hnear (n : ℕ) : ∃ z ∈ range p, dist (w n) z < 1 / ((n : ℝ)+1) :=
    (Metric.mem_closure_iff.mp (hw n)) _ (by positivity)
  choose z hz hdist using hnear
  choose t ht using hz
  obtain ⟨k, hk, a, hpa⟩ := hpseq t
  have hza : Tendsto (fun n => z (k n)) atTop (𝓝 a) := by
    simpa only [ht] using hpa
  have haz : a ∈ closure (range p) :=
    isClosed_closure.mem_of_tendsto hza (Eventually.of_forall fun n => subset_closure ⟨t (k n), ht (k n)⟩)
  have hdist0 : Tendsto (fun n => dist (z n) (w n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg)
      (fun n => by simpa only [dist_comm] using (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨a, haz, k, hk, ?_⟩
  exact hza.congr_dist (hdist0.comp hk.tendsto_atTop)

end HartreeF.ActualCompactOrbitGauge
