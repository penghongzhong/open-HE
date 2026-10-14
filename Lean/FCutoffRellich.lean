import FCutoffH1Operators
import FRellichWeakLimit

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace HartreeF.LocalRellich
open EnergySpace SobolevStretch CutoffApproximation
attribute [local irreducible] energySubmodule
attribute [local instance 101] secondCountableTopologyEither_of_left

/-- Real projections of the actual cutoff L2 value. -/
def cutoffScalarValue (L : ℂ →L[ℝ] ℝ) (k : ℕ) :
    EnergyState →L[ℝ] Lp ℝ 2 (volume : Measure Space) :=
  (L.compLpL 2 volume).comp (cutoffValue k)

theorem cutoffScalarValue_ae (L : ℂ →L[ℝ] ℝ) (k : ℕ) (u : EnergyState) :
    (cutoffScalarValue L k u : Space → ℝ) =ᵐ[volume]
      fun x => cutoff k x * L (energyValue u x) := by
  filter_upwards [L.coeFn_compLpL (cutoffValue k u), cutoffValue_ae k u] with x hx hχ
  exact hx.trans (by rw [hχ, map_smul]; rfl)

/-- Ordinary real ball Rellich applied to the actual cutoff/product-rule fields.
All scalar L2 domains and uniform H1 bounds are produced here from EnergyState. -/
theorem cutoffScalarValue_rellich_cauchy (hRel : OrdinaryRellichBall)
    (L : ℂ →L[ℝ] ℝ) (k : ℕ) {u : ℕ → EnergyState} {B : ℝ}
    (hB : ∀ n, ‖u n‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ CauchySeq (fun n => cutoffScalarValue L k (u (σ n))) := by
  let v (n : ℕ) (x : Space) := cutoff k x * L (energyValue (u n) x)
  let G (n : ℕ) (x : Space) := cutoff k x • energyProjectedGradient L (u n) x +
    L (energyValue (u n) x) • gradient (cutoff k) x
  have hv (n) : MemLp (v n) 2 volume :=
    (Lp.memLp (cutoffScalarValue L k (u n))).ae_eq (cutoffScalarValue_ae L k (u n))
  have hG (n) : MemLp (G n) 2 volume :=
    (Lp.memLp (cutoffGradient L k (u n))).ae_eq (cutoffGradient_ae L k (u n))
  have hw (n) : HasWeakGradient (v n) (G n) :=
    (energyState_hasWeakGradient L (u n)).mul_smooth (cutoff_smooth k)
  have hs (n) : Function.support (v n) ⊆ Metric.ball 0 (2*((k:ℝ)+1)) := by
    intro x hx
    by_contra hnot
    have hz := cutoff_eq_zero k (le_of_not_gt (by simpa only [Metric.mem_ball, dist_zero_right] using hnot))
    exact hx (by simp [v, hz])
  have hn (n) : (eLpNorm (v n) 2 volume).toReal = ‖cutoffScalarValue L k (u n)‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (cutoffScalarValue_ae L k (u n))]
  have hgn (n) : (eLpNorm (G n) 2 volume).toReal = ‖cutoffGradient L k (u n)‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (cutoffGradient_ae L k (u n))]
  have hb : ∃ C : ℝ, ∀ n, (eLpNorm (v n) 2 volume).toReal + (eLpNorm (G n) 2 volume).toReal ≤ C := by
    refine ⟨(‖cutoffScalarValue L k‖ + ‖cutoffGradient L k‖)*B, fun n => ?_⟩
    rw [hn, hgn]
    exact cutoff_h1_uniform_bound L k hB n
  obtain ⟨σ,hσ,hc⟩ := rellich_supported_cauchy hRel (by positivity : 0 < 2*((k:ℝ)+1)) hw hv hG hs hb
  have he (n) : (hv n).toLp (v n) = cutoffScalarValue L k (u n) := by
    apply Lp.ext
    exact (hv n).coeFn_toLp.trans (cutoffScalarValue_ae L k (u n)).symm
  exact ⟨σ,hσ,by simpa only [he] using hc⟩

/-- The named gradient-weak limit is identified natively through all actual
EnergyState functionals; no weak-value or local-strong premise is assumed. -/
theorem cutoffScalarValue_tendsto (hRel : OrdinaryRellichBall)
    {K : ℝ} (hSob : OrdinarySobolev K) (L : ℂ →L[ℝ] ℝ) (k : ℕ)
    {u : ℕ → EnergyState} {f : EnergyState} {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B)
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (u n)) v) atTop
        (𝓝 (inner ℝ (energyGradient j f) v))) :
    Tendsto (fun n => cutoffScalarValue L k (u n)) atTop (𝓝 (cutoffScalarValue L k f)) := by
  apply tendsto_of_weak_of_subsequence_cauchy
  · intro v
    have ht := energyState_dual_tendsto_of_gradient_weak hSob hweak
      ((innerSL ℝ v).comp (cutoffScalarValue L k))
    change Tendsto (fun n => inner ℝ v (cutoffScalarValue L k (u n))) atTop
      (𝓝 (inner ℝ v (cutoffScalarValue L k f))) at ht
    simpa only [real_inner_comm] using ht
  · intro σ _
    exact cutoffScalarValue_rellich_cauchy hRel L k (u := fun n => u (σ n)) (B := B)
      (fun n => hB (σ n))

/-- Reconstruction of an actual complex L2 class from its two real parts. -/
theorem l2_recompose (a : L2) :
    Complex.ofRealCLM.compLpL 2 volume (Complex.reCLM.compLpL 2 volume a) +
      (Complex.I • Complex.ofRealCLM).compLpL 2 volume (Complex.imCLM.compLpL 2 volume a) = a := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
    (Complex.ofRealCLM.compLpL 2 volume (Complex.reCLM.compLpL 2 volume a))
    ((Complex.I • Complex.ofRealCLM).compLpL 2 volume (Complex.imCLM.compLpL 2 volume a)),
    Complex.ofRealCLM.coeFn_compLpL (Complex.reCLM.compLpL 2 volume a),
    (Complex.I • Complex.ofRealCLM).coeFn_compLpL (Complex.imCLM.compLpL 2 volume a),
    Complex.reCLM.coeFn_compLpL a, Complex.imCLM.coeFn_compLpL a] with x ha hr hi hre him
  rw [ha, Pi.add_apply, hr, hi, hre, him]
  change ((a x).re : ℂ) + Complex.I * ((a x).im : ℂ) = a x
  simpa only [mul_comm] using Complex.re_add_im (a x)

/-- Actual fixed-cutoff complex L2 convergence from bounded homogeneous states
and the exact coordinate-gradient weak convergence used by the BL gate. -/
theorem cutoffValue_tendsto (hRel : OrdinaryRellichBall)
    {K : ℝ} (hSob : OrdinarySobolev K) (k : ℕ)
    {u : ℕ → EnergyState} {f : EnergyState} {B : ℝ} (hB : ∀ n, ‖u n‖ ≤ B)
    (hweak : ∀ j : Fin 3, ∀ v : L2,
      Tendsto (fun n => inner ℝ (energyGradient j (u n)) v) atTop
        (𝓝 (inner ℝ (energyGradient j f) v))) :
    Tendsto (fun n => cutoffValue k (u n)) atTop (𝓝 (cutoffValue k f)) := by
  have hr := (Complex.ofRealCLM.compLpL 2 volume).continuous.tendsto
      (cutoffScalarValue Complex.reCLM k f) |>.comp
    (cutoffScalarValue_tendsto hRel hSob Complex.reCLM k hB hweak)
  have hi := ((Complex.I • Complex.ofRealCLM).compLpL 2 volume).continuous.tendsto
      (cutoffScalarValue Complex.imCLM k f) |>.comp
    (cutoffScalarValue_tendsto hRel hSob Complex.imCLM k hB hweak)
  simpa only [Function.comp_def, cutoffScalarValue, ContinuousLinearMap.comp_apply, l2_recompose]
    using hr.add hi

#print axioms cutoffScalarValue_ae
#print axioms cutoffScalarValue_rellich_cauchy
#print axioms cutoffScalarValue_tendsto
#print axioms l2_recompose
#print axioms cutoffValue_tendsto
end HartreeF.LocalRellich
