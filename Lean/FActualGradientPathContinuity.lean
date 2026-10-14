import FCriticalHartreeSourceSmallness

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

universe uTime

namespace HartreeF.CriticalSourceBounds
open EnergySpace CriticalPathSpace CriticalTimeSobolev TimeHolder SobolevStretch
open StationarySelfTest ForcingDomain GradientMajorants WeakHartreeProduct CriticalJointSources
attribute [local irreducible] jointFields energySubmodule criticalPathSubmodule
  energyPath criticalGradient energyValue energyGradient

/-- The finite coefficient left after all three differences are bounded by delta. -/
def gradientDifferenceCoefficient (alpha : ℝ) (M N Y : ℝ≥0∞) : ℝ≥0∞ :=
  M ^ (2 * alpha) * N ^ (4 : ℝ) +
    M ^ (2 * alpha) * N ^ (3 : ℝ) * Y +
    M ^ (5 * alpha / 3) * N ^ (4 - theta alpha) * Y

theorem gradientDifferenceCoefficient_mono {alpha : ℝ} (ha : 0 < alpha)
    {M N Y M' N' Y' : ℝ≥0∞} (hM : M ≤ M') (hN : N ≤ N') (hY : Y ≤ Y') :
    gradientDifferenceCoefficient alpha M N Y ≤
      gradientDifferenceCoefficient alpha M' N' Y' := by
  have h2 : 0 ≤ 2 * alpha := by positivity
  have h5 : 0 ≤ 5 * alpha / 3 := by positivity
  have ht : 0 ≤ 4 - theta alpha := by unfold theta; linarith
  unfold gradientDifferenceCoefficient
  gcongr

theorem gradientDifferenceCoefficient_ne_top {alpha : ℝ} (ha : 0 < alpha)
    {M N Y : ℝ≥0∞} (hM : M ≠ ∞) (hN : N ≠ ∞) (hY : Y ≠ ∞) :
    gradientDifferenceCoefficient alpha M N Y ≠ ∞ := by
  have h2 : 0 ≤ 2 * alpha := by positivity
  have h5 : 0 ≤ 5 * alpha / 3 := by positivity
  have ht : 0 ≤ 4 - theta alpha := by unfold theta; linarith
  unfold gradientDifferenceCoefficient
  finiteness

theorem normComparisonConstant_lower_bounds {K : ℝ} (hSob : OrdinarySobolev K) :
    (1 : ℝ) ≤ normComparisonConstant K ∧ (6 : ℝ) ≤ normComparisonConstant K ∧
      ((5/3 : ℝ)*K^(1/6 : ℝ))*6 ≤ normComparisonConstant K := by
  have hK := hSob.nonneg
  have hS : 0 ≤ (5/3 : ℝ)*K^(1/6 : ℝ) := by positivity
  unfold normComparisonConstant
  constructor
  · linarith
  constructor <;> linarith

/-- Abstract norm-space argument keeps metric normalization out of the path wrapper. -/
theorem mixedSize_tendsto_zero_of_norm_ball_bounds
    {X : Type*} [NormedAddCommGroup X] (a : X → X → ℝ≥0∞)
    (hballs : ∀ B : ℝ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ z w : X,
      ‖z‖ ≤ B → ‖w‖ ≤ B → a z w ≤ C * ENNReal.ofReal ‖z-w‖)
    {I : Type*} {l : Filter I} (z : I → X) (w : X) (hz : Tendsto z l (𝓝 w)) :
    Tendsto (fun i => a (z i) w) l (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := hballs (‖w‖+1)
  have hd : Tendsto (fun i => ‖z i-w‖) l (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hz
  have he : ∀ᶠ i in l, ‖z i-w‖ < 1 := hd.eventually (gt_mem_nhds (by norm_num))
  have hd' : Tendsto (fun i => ENNReal.ofReal ‖z i-w‖) l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hd
  have ht : Tendsto (fun i => C * ENNReal.ofReal ‖z i-w‖) l (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hd' (Or.inr hC)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [he] with i hi
  apply hbound (z i) w
  · have hh := norm_le_norm_sub_add (z i) w
    linarith
  · linarith

/-- The accepted full-gradient estimate specialized before path-space elaboration. -/
theorem actual_gradient_fixed_measure_bound
    {T : Type uTime} [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
    {alpha c : ℝ} (hH : OrdinaryHLS alpha c) :
    ∃ C : ℝ≥0, ∀
    (u v : T → Space → ℂ) (U V P Q : T → Space → Space)
    (_ : ∀ᵐ t ∂μ, InDotH1 (u t) (U t) (V t) ∧ InDotH1 (v t) (P t) (Q t) ∧
        MemLp (u t) 10 volume ∧ MemLp (v t) 10 volume ∧
        MemLp (U t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (V t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (P t) (ENNReal.ofReal (30/13 : ℝ)) volume ∧
        MemLp (Q t) (ENNReal.ofReal (30/13 : ℝ)) volume)
    (_ : AEStronglyMeasurable (fun z : T × Space => u z.1 z.2) (μ.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => v z.1 z.2) (μ.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => U z.1 z.2) (μ.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => V z.1 z.2) (μ.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => P z.1 z.2) (μ.prod volume))
    (_ : AEStronglyMeasurable (fun z : T × Space => Q z.1 z.2) (μ.prod volume)),
    mixedNorm μ volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c (u t) (U t) (V t) -
        actualFullGradient alpha c (v t) (P t) (Q t)) ≤
      (C : ℝ≥0∞) * vectorDifferenceBudget alpha μ u v U V P Q := by
  exact (actual_full_gradient_vector_difference_bound.{uTime} hH).imp
    (fun _ hC => @hC T inferInstance μ inferInstance)

section PathBounds
variable {T : Type uTime} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
  [BorelSpace T] (μ : Measure T) [SigmaFinite μ]

/-- All source input sizes are bounded by one constant times the E+W path norm. -/
theorem joint_sizes_common_norm_bound (hDensity : OrdinaryH1Density) {K : ℝ}
    (hSob : OrdinarySobolev K) (z : CriticalPath μ) :
    pathEnergySize μ z ≤ ENNReal.ofReal (normComparisonConstant K) * ENNReal.ofReal ‖z‖ ∧
    pathValueSize μ z ≤ ENNReal.ofReal (normComparisonConstant K) * ENNReal.ofReal ‖z‖ ∧
    pathGradientSize μ z ≤ ENNReal.ofReal (normComparisonConstant K) * ENNReal.ofReal ‖z‖ := by
  obtain ⟨h1, h6, hS6⟩ := normComparisonConstant_lower_bounds hSob
  have hK := hSob.nonneg
  have hS : 0 ≤ (5/3 : ℝ)*K^(1/6 : ℝ) := by positivity
  have hW := (joint_gradient_bound μ z).trans
    (mul_le_mul' (show (6 : ℝ≥0∞) ≤ ENNReal.ofReal (normComparisonConstant K) by
      simpa using ENNReal.ofReal_le_ofReal h6) le_rfl)
  refine ⟨?_, ?_, hW⟩
  · exact (joint_value_energy_bound μ z).trans (by
      calc
        _ = 1 * ENNReal.ofReal ‖z‖ := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal h1) le_rfl)
  · have hb := (joint_value_critical_bound μ hDensity hSob z).trans
      (mul_le_mul' le_rfl (joint_gradient_bound μ z))
    rw [← mul_assoc] at hb
    exact hb.trans (mul_le_mul' (show ENNReal.ofReal ((5/3)*K^(1/6 : ℝ)) * 6 ≤
      ENNReal.ofReal (normComparisonConstant K) by
        simpa only [ENNReal.ofReal_mul hS, ENNReal.ofReal_ofNat] using
          ENNReal.ofReal_le_ofReal hS6) le_rfl)

/-- A finite Lipschitz coefficient controls the actual full Hartree gradient on every
ball of the complete E+W path norm. -/
theorem actualGradientSize_bounded_ball_lipschitz (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c) (B : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (z w : CriticalPath μ),
    ‖z‖ ≤ B → ‖w‖ ≤ B →
    actualGradientSize μ alpha c z w ≤ C * ENNReal.ofReal ‖z-w‖ := by
  let hExists := actual_gradient_fixed_measure_bound μ hH
  let C : ℝ≥0 := Classical.choose hExists
  let L : ℝ≥0∞ := ENNReal.ofReal (normComparisonConstant K)
  let A : ℝ≥0∞ := L * ENNReal.ofReal B
  let P := gradientDifferenceCoefficient alpha (2*A) (2*A) A
  have hL : L ≠ ∞ := ENNReal.ofReal_ne_top
  have hA : A ≠ ∞ := ENNReal.mul_ne_top hL ENNReal.ofReal_ne_top
  have h2A : 2*A ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hA
  have hP : P ≠ ∞ := gradientDifferenceCoefficient_ne_top hH.order_pos h2A h2A hA
  refine ⟨(C : ℝ≥0∞)*P*L, ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.coe_ne_top hP) hL, ?_⟩
  intro z w hz hw
  have hsize (v : CriticalPath μ) (hv : ‖v‖ ≤ B) :
      pathEnergySize μ v ≤ A ∧ pathValueSize μ v ≤ A ∧ pathGradientSize μ v ≤ A := by
    have hh := joint_sizes_common_norm_bound μ hDensity hSob v
    have hb : L * ENNReal.ofReal ‖v‖ ≤ A :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hv)
    exact ⟨hh.1.trans hb, hh.2.1.trans hb, hh.2.2.trans hb⟩
  have hsz := hsize z hz
  have hsw := hsize w hw
  have hM : pathEnergySize μ z + pathEnergySize μ w ≤ 2*A :=
    (add_le_add hsz.1 hsw.1).trans_eq (two_mul A).symm
  have hN : pathValueSize μ z + pathValueSize μ w ≤ 2*A :=
    (add_le_add hsz.2.1 hsw.2.1).trans_eq (two_mul A).symm
  let delta : ℝ≥0∞ := L * ENNReal.ofReal ‖z-w‖
  obtain ⟨h1, h6, hS6⟩ := normComparisonConstant_lower_bounds hSob
  have hK := hSob.nonneg
  have hS : 0 ≤ (5/3 : ℝ)*K^(1/6 : ℝ) := by positivity
  have hD := (joint_value_difference_energy_bound μ z w).trans
    (show ENNReal.ofReal ‖z-w‖ ≤ delta from by
      calc
        _ = 1 * ENNReal.ofReal ‖z-w‖ := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (by simpa [L] using ENNReal.ofReal_le_ofReal h1) le_rfl)
  have hZ := (joint_gradient_difference_bound μ z w).trans
    (mul_le_mul' (show (6 : ℝ≥0∞) ≤ L by simpa [L] using ENNReal.ofReal_le_ofReal h6) le_rfl)
  have hE := (joint_value_difference_critical_bound μ hDensity hSob z w).trans
    (mul_le_mul' (show ENNReal.ofReal ((5/3)*K^(1/6 : ℝ)) * 6 ≤ L by
      simpa only [L, ENNReal.ofReal_mul hS, ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal hS6) le_rfl)
  have hC := Classical.choose_spec hExists
  have hb := hC (jointFields μ z).u (jointFields μ w).u
    (jointFields μ z).U (jointFields μ z).V (jointFields μ w).U (jointFields μ w).V
    (joint_slices μ hDensity hSob z w)
    (jointFields μ z).joint_u.aestronglyMeasurable (jointFields μ w).joint_u.aestronglyMeasurable
    (jointFields μ z).joint_U.aestronglyMeasurable (jointFields μ z).joint_V.aestronglyMeasurable
    (jointFields μ w).joint_U.aestronglyMeasurable (jointFields μ w).joint_V.aestronglyMeasurable
  have hbudget := criticalBudget_le_delta hH.order_pos hH.order_lt_three
    (pathEnergySize μ z + pathEnergySize μ w) (pathValueSize μ z + pathValueSize μ w)
    _ _ (pathGradientSize μ w) _ delta hD hE hZ
  have hc := gradientDifferenceCoefficient_mono hH.order_pos hM hN hsw.2.2
  have hfinal := hb.trans (mul_le_mul' le_rfl
    (hbudget.trans (mul_le_mul' hc le_rfl)))
  simpa only [vectorDifferenceBudget, pathEnergySize, pathValueSize, pathGradientSize,
    gradientDifferenceCoefficient, P, delta, C, actualGradientSize, mul_assoc] using hfinal

/-- E+W path convergence gives actual gradient forcing convergence in L²_t L^{6/5}_x.
The paths use the canonical L⁶ energy state; no original-function L² assumption occurs. -/
theorem actualGradientSize_tendsto_zero (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    {I : Type*} {l : Filter I} (z : I → CriticalPath μ) (w : CriticalPath μ)
    (hz : Tendsto z l (𝓝 w)) :
    Tendsto (fun i => actualGradientSize μ alpha c (z i) w) l (𝓝 0) :=
  mixedSize_tendsto_zero_of_norm_ball_bounds (actualGradientSize μ alpha c)
    (actualGradientSize_bounded_ball_lipschitz μ hDensity hSob hH) z w hz

/-- Literal mixed-norm form of the actual gradient continuity statement. -/
theorem actual_full_gradient_mixed_tendsto_zero (hDensity : OrdinaryH1Density)
    {K alpha c : ℝ} (hSob : OrdinarySobolev K) (hH : OrdinaryHLS alpha c)
    {I : Type*} {l : Filter I} (z : I → CriticalPath μ) (w : CriticalPath μ)
    (hz : Tendsto z l (𝓝 w)) :
    Tendsto (fun i => mixedNorm μ volume 2 (ENNReal.ofReal (6/5 : ℝ))
      (fun t => actualFullGradient alpha c ((jointFields μ (z i)).u t)
        ((jointFields μ (z i)).U t) ((jointFields μ (z i)).V t) -
        actualFullGradient alpha c ((jointFields μ w).u t)
          ((jointFields μ w).U t) ((jointFields μ w).V t))) l (𝓝 0) :=
  actualGradientSize_tendsto_zero μ hDensity hSob hH z w hz

end PathBounds

#print axioms mixedSize_tendsto_zero_of_norm_ball_bounds
#print axioms actual_gradient_fixed_measure_bound
#print axioms gradientDifferenceCoefficient_mono
#print axioms gradientDifferenceCoefficient_ne_top
#print axioms joint_sizes_common_norm_bound
#print axioms actualGradientSize_bounded_ball_lipschitz
#print axioms actualGradientSize_tendsto_zero
#print axioms actual_full_gradient_mixed_tendsto_zero
end HartreeF.CriticalSourceBounds
