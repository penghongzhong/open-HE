import FCriticalAffineIsometry
import FEnergyGradientTopology
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! Actual affine parameter/data continuity in the original energy-state topology.
The auxiliary action is on the existing complex L2 coordinate gradients. Schwartz
density is used once, after a single fixed-target dominated pairing calculation.
No L2 assumption is made on an energy state's value. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Filter Set
open scoped ENNReal Topology SchwartzMap
namespace HartreeF.CriticalAffine
open EnergySpace SobolevStretch

/-- The genuine L2 class of the critical gradient pullback. -/
def gradientAffineL2Value {a : ℝ} (ha : 0 < a) (b : Space) (G : L2) : L2 :=
  (gradientPullback_memLp ha b (by norm_num) (by norm_num) (Lp.memLp G)).toLp
    (gradientPullback a b G)

theorem gradientAffineL2Value_ae {a : ℝ} (ha : 0 < a) (b : Space) (G : L2) :
    (gradientAffineL2Value ha b G : Space → ℂ) =ᵐ[volume] gradientPullback a b G :=
  (gradientPullback_memLp ha b (by norm_num) (by norm_num) (Lp.memLp G)).coeFn_toLp

theorem gradientAffineL2Value_add {a : ℝ} (ha : 0 < a) (b : Space) (G H : L2) :
    gradientAffineL2Value ha b (G + H) =
      gradientAffineL2Value ha b G + gradientAffineL2Value ha b H := by
  apply Lp.ext
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae (Lp.coeFn_add G H)
  filter_upwards [gradientAffineL2Value_ae ha b (G + H),
    gradientAffineL2Value_ae ha b G, gradientAffineL2Value_ae ha b H,
    Lp.coeFn_add (gradientAffineL2Value ha b G) (gradientAffineL2Value ha b H), hi]
    with x hs hG hH ho hi
  simp only [gradientPullback] at hs hG hH
  simp only [Pi.add_apply] at hi ho
  rw [hs, hi, smul_add, ho, hG, hH]

theorem gradientAffineL2Value_smul {a : ℝ} (ha : 0 < a) (b : Space) (c : ℂ)
    (G : L2) : gradientAffineL2Value ha b (c • G) = c • gradientAffineL2Value ha b G := by
  apply Lp.ext
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae (Lp.coeFn_smul c G)
  filter_upwards [gradientAffineL2Value_ae ha b (c • G),
    gradientAffineL2Value_ae ha b G, Lp.coeFn_smul c (gradientAffineL2Value ha b G), hi]
    with x hs hG ho hi
  simp only [gradientPullback] at hs hG
  simp only [Pi.smul_apply] at hi ho
  rw [hs, hi, ho, hG]
  exact smul_comm _ _ _

theorem gradientAffineL2Value_norm {a : ℝ} (ha : 0 < a) (b : Space) (G : L2) :
    ‖gradientAffineL2Value ha b G‖ = ‖G‖ := by
  let : Fact ((1 : ℝ≥0∞) ≤ (2 : ℕ)) := ⟨by norm_num⟩
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : (2 : ℕ) ≠ 0)).mp
  rw [energyLp_norm_pow (by decide : (2 : ℕ) ≠ 0),
    energyLp_norm_pow (by decide : (2 : ℕ) ≠ 0)]
  calc
    _ = ∫ x, ‖gradientPullback a b G x‖ ^ 2 := by
      apply integral_congr_ae
      exact (gradientAffineL2Value_ae ha b G).mono
        (fun _ h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)
    _ = _ := gradientPullback_square_integral ha b G

/-- The critical gradient pullback is an actual complex linear isometry. -/
def gradientAffineL2 {a : ℝ} (ha : 0 < a) (b : Space) : L2 →ₗᵢ[ℂ] L2 where
  toFun := gradientAffineL2Value ha b
  map_add' := gradientAffineL2Value_add ha b
  map_smul' := gradientAffineL2Value_smul ha b
  norm_map' := gradientAffineL2Value_norm ha b

theorem gradientAffineL2_ae {a : ℝ} (ha : 0 < a) (b : Space) (G : L2) :
    (gradientAffineL2 ha b G : Space → ℂ) =ᵐ[volume] gradientPullback a b G :=
  gradientAffineL2Value_ae ha b G

/-- This class equality connects the auxiliary action to the actual state. -/
theorem energyGradient_affineState {a : ℝ} (ha : 0 < a) (b : Space)
    (u : EnergyState) (j : Fin 3) :
    energyGradient j (affineState ha b u) = gradientAffineL2 ha b (energyGradient j u) := by
  apply Lp.ext
  exact (affineState_gradient_ae ha b u j).trans
    (gradientAffineL2_ae ha b (energyGradient j u)).symm

private theorem gradientAffineL2_schwartz_ae {a : ℝ} (ha : 0 < a) (b : Space)
    (φ : Test) : (gradientAffineL2 ha b (φ.toLp 2 volume) : Space → ℂ) =ᵐ[volume]
      gradientPullback a b φ := by
  have hi := (affine_quasiMeasurePreserving ha.ne' b).ae (φ.coeFn_toLp 2 volume)
  filter_upwards [gradientAffineL2_ae ha b (φ.toLp 2 volume), hi] with x hx hi
  simpa only [gradientPullback, hi] using hx

private theorem gradientAffineL2_schwartz_pairing {a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (b d : Space) (φ : Test) :
    inner ℂ (gradientAffineL2 ha b (φ.toLp 2 volume))
      (gradientAffineL2 hc d (φ.toLp 2 volume)) =
        ∫ x, inner ℂ (gradientPullback a b φ x) (gradientPullback c d φ x) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [gradientAffineL2_schwartz_ae ha b φ,
    gradientAffineL2_schwartz_ae hc d φ] with x hx hy
  rw [hx, hy]

/-- One fixed limiting affine Schwartz target supplies an integrable L1
dominator, so no varying-L2 representative composition theorem is needed. -/
private theorem gradientAffineL2_schwartz_pairing_tendsto
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    {a0 : ℝ} (ha0 : 0 < a0) {b0 : Space}
    (ha_lim : Tendsto a atTop (𝓝 a0)) (hb_lim : Tendsto b atTop (𝓝 b0)) (φ : Test) :
    Tendsto (fun n => inner ℂ (gradientAffineL2 ha0 b0 (φ.toLp 2 volume))
      (gradientAffineL2 (ha n) (b n) (φ.toLp 2 volume))) atTop
      (𝓝 (inner ℂ (gradientAffineL2 ha0 b0 (φ.toLp 2 volume))
        (gradientAffineL2 ha0 b0 (φ.toLp 2 volume)))) := by
  simp_rw [gradientAffineL2_schwartz_pairing]
  let C : ℝ := a0 * Real.sqrt a0 + 1
  let ψ : Space → ℂ := gradientPullback a0 b0 φ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcoeff : Tendsto (fun n => a n * Real.sqrt (a n)) atTop
      (𝓝 (a0 * Real.sqrt a0)) :=
    ha_lim.mul ((Real.continuous_sqrt.tendsto a0).comp ha_lim)
  have hbound : ∀ᶠ n in atTop, a n * Real.sqrt (a n) ≤ C :=
    (hcoeff.eventually (eventually_lt_nhds
      (show a0 * Real.sqrt a0 < C by dsimp [C]; linarith))).mono
      (fun _ hn => hn.le)
  have hψ : Integrable ψ volume :=
    (affine_integrable ha0.ne' b0 φ.integrable).smul (a0 * Real.sqrt a0)
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun x => (C * SchwartzMap.seminorm ℝ 0 0 φ) * ‖ψ x‖)
  · exact Eventually.of_forall fun n =>
      (by unfold gradientPullback affine; fun_prop : Continuous
        (fun x => inner ℂ (gradientPullback a0 b0 φ x)
          (gradientPullback (a n) (b n) φ x))).aestronglyMeasurable
  · filter_upwards [hbound] with n hn
    exact Eventually.of_forall fun x => by
      have hcoeff0 : 0 ≤ a n * Real.sqrt (a n) :=
        mul_nonneg (ha n).le (Real.sqrt_nonneg _)
      calc
        ‖inner ℂ (gradientPullback a0 b0 φ x) (gradientPullback (a n) (b n) φ x)‖
            ≤ ‖ψ x‖ * ‖gradientPullback (a n) (b n) φ x‖ := norm_inner_le_norm _ _
        _ = ((a n * Real.sqrt (a n)) * ‖φ (affine (a n) (b n) x)‖) * ‖ψ x‖ := by
          rw [gradientPullback, norm_smul, Real.norm_of_nonneg hcoeff0]
          ring
        _ ≤ (C * SchwartzMap.seminorm ℝ 0 0 φ) * ‖ψ x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hn (SchwartzMap.norm_le_seminorm ℝ φ _)
              (norm_nonneg _) hC) (norm_nonneg _)
  · exact hψ.norm.const_mul _
  · apply Eventually.of_forall
    intro x
    have hx : Tendsto (fun n => affine (a n) (b n) x) atTop (𝓝 (affine a0 b0 x)) :=
      (ha_lim.smul tendsto_const_nhds).add hb_lim
    have hφ : Tendsto (fun n => gradientPullback (a n) (b n) φ x) atTop
        (𝓝 (gradientPullback a0 b0 φ x)) :=
      hcoeff.smul ((φ.continuous.tendsto _).comp hx)
    exact tendsto_const_nhds.inner hφ

/-- The Hilbert equal-norm argument, using only the pairing against the
fixed proposed limit. This is the ordinary D AffineProperness proof body. -/
private theorem l2_tendsto_of_pairing_of_norm (v : ℕ → L2) (f : L2)
    (hn : ∀ n, ‖v n‖ = ‖f‖)
    (hw : Tendsto (fun n => inner ℂ f (v n)) atTop (𝓝 (inner ℂ f f))) :
    Tendsto v atTop (𝓝 f) := by
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hw
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  have hsq : Tendsto (fun n => ‖v n - f‖ ^ 2) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖f‖ ^ 2) atTop
      (𝓝 (‖f‖ ^ 2))).sub (hr.const_mul 2)).add_const (‖f‖ ^ 2)
    convert hh using 1
    · funext n
      rw [norm_sub_rev, norm_sub_sq (𝕜 := ℂ), hn n]
      rfl
    · rw [hself]
      congr 1
      ring
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun n => Real.sqrt (‖v n - f‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at hh
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

private theorem gradientAffineL2_schwartz_tendsto
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    {a0 : ℝ} (ha0 : 0 < a0) {b0 : Space}
    (ha_lim : Tendsto a atTop (𝓝 a0)) (hb_lim : Tendsto b atTop (𝓝 b0)) (φ : Test) :
    Tendsto (fun n => gradientAffineL2 (ha n) (b n) (φ.toLp 2 volume)) atTop
      (𝓝 (gradientAffineL2 ha0 b0 (φ.toLp 2 volume))) := by
  apply l2_tendsto_of_pairing_of_norm
  · intro n
    simp only [LinearIsometry.norm_map]
  · exact gradientAffineL2_schwartz_pairing_tendsto a ha b ha0 ha_lim hb_lim φ

/-- Strong continuity on each actual L2 datum, extended once from Schwartz
by Mathlib's closed convergence locus for equicontinuous families. -/
theorem gradientAffineL2_tendsto
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    {a0 : ℝ} (ha0 : 0 < a0) {b0 : Space}
    (ha_lim : Tendsto a atTop (𝓝 a0)) (hb_lim : Tendsto b atTop (𝓝 b0)) (G : L2) :
    Tendsto (fun n => gradientAffineL2 (ha n) (b n) G) atTop
      (𝓝 (gradientAffineL2 ha0 b0 G)) := by
  have hEq : Equicontinuous (fun n G => gradientAffineL2 (ha n) (b n) G) :=
    (LipschitzWith.uniformEquicontinuous (fun n G => gradientAffineL2 (ha n) (b n) G)
      1 (fun n => (gradientAffineL2 (ha n) (b n)).lipschitzWith)).equicontinuous
  have hclosed : IsClosed {G : L2 | Tendsto
      (fun n => gradientAffineL2 (ha n) (b n) G) atTop (𝓝 (gradientAffineL2 ha0 b0 G))} :=
    hEq.isClosed_setOfPred_tendsto (gradientAffineL2 ha0 b0).continuous
  exact (SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := Space) (p := 2)
    (μ := (volume : Measure Space)) (by norm_num)).induction_on G hclosed
      (fun φ => gradientAffineL2_schwartz_tendsto a ha b ha0 ha_lim hb_lim φ)

/-- Moving L2 data add an error whose norm is unchanged by every parameter. -/
theorem gradientAffineL2_tendsto_data
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    {a0 : ℝ} (ha0 : 0 < a0) {b0 : Space}
    (ha_lim : Tendsto a atTop (𝓝 a0)) (hb_lim : Tendsto b atTop (𝓝 b0))
    (G : ℕ → L2) {G0 : L2} (hG_lim : Tendsto G atTop (𝓝 G0)) :
    Tendsto (fun n => gradientAffineL2 (ha n) (b n) (G n)) atTop
      (𝓝 (gradientAffineL2 ha0 b0 G0)) := by
  have he : Tendsto (fun n => gradientAffineL2 (ha n) (b n) (G n - G0)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [LinearIsometry.norm_map] using tendsto_iff_norm_sub_tendsto_zero.mp hG_lim
  have hh := he.add (gradientAffineL2_tendsto a ha b ha0 ha_lim hb_lim G0)
  simpa only [map_sub, sub_add_cancel, zero_add] using hh

/-- Actual affine parameter/data convergence in the original EnergyState
graph norm. Sobolev supplies the L6 coordinate from the proved L2 gradients. -/
theorem affineState_tendsto_data {K : ℝ} (hSob : OrdinarySobolev K)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (b : ℕ → Space)
    {a0 : ℝ} (ha0 : 0 < a0) {b0 : Space}
    (ha_lim : Tendsto a atTop (𝓝 a0)) (hb_lim : Tendsto b atTop (𝓝 b0))
    (u : ℕ → EnergyState) {u0 : EnergyState} (hu_lim : Tendsto u atTop (𝓝 u0)) :
    Tendsto (fun n => affineState (ha n) (b n) (u n)) atTop
      (𝓝 (affineState ha0 b0 u0)) := by
  apply EnergySpace.tendsto_of_gradientTendsto hSob
  intro j
  simp only [energyGradient_affineState]
  exact gradientAffineL2_tendsto_data a ha b ha0 ha_lim hb_lim
    (fun n => energyGradient j (u n)) (gradientTendsto_of_tendsto hu_lim j)

/-- In the paper convention, inverse normalization has the direct positive
scale and center parameters of affineState. -/
theorem criticalAffineState_symm_eq_affineState (R : ℝ) (hR : 0 < R)
    (x : Space) (u : EnergyState) :
    (criticalAffineState R hR x).symm u = affineState hR x u := by
  change affineState (inv_pos.mpr (inv_pos.mpr hR)) (-((R⁻¹)⁻¹ • -(R⁻¹ • x))) u = _
  simp only [inv_inv, smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

/-- Exact relative state identity for the intrinsic gauge and extracted PS
frames; all equalities are in the original EnergyState class. -/
theorem criticalAffineState_symm_apply_relative (R lambda : ℝ)
    (hR : 0 < R) (hlambda : 0 < lambda) (x y : Space) (v : EnergyState) :
    (criticalAffineState R hR x).symm (criticalAffineState lambda hlambda y v) =
      affineState (div_pos hR hlambda) (lambda⁻¹ • (x - y)) v := by
  rw [criticalAffineState_symm_eq_affineState]
  change affineState hR x (affineState (inv_pos.mpr hlambda) (-(lambda⁻¹ • y)) v) = _
  simpa only [div_eq_mul_inv, mul_comm, smul_sub, sub_eq_add_neg, smul_add, smul_neg] using
    affineState_comp hR (inv_pos.mpr hlambda) x (-(lambda⁻¹ • y)) v

#print axioms gradientAffineL2
#print axioms energyGradient_affineState
#print axioms gradientAffineL2_tendsto
#print axioms gradientAffineL2_tendsto_data
#print axioms affineState_tendsto_data
#print axioms criticalAffineState_symm_apply_relative
end HartreeF.CriticalAffine
