import FCompatibleL1IntervalSource
import FIntervalRetardedPathDifference
import FActualFreePathDifference

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Filter LineDeriv
open scoped ENNReal Topology
namespace HartreeF.ActualDuhamelPath
open CriticalPathSpace IntervalTimeTransport EnergySpace ForcingDomain
open SobolevStretch StationarySelfTest Retarded ActualStrichartz
attribute [local instance] FreeDataDependence.canonicalEnergyNormedSpace
  FreeDataDependence.canonicalPathNormedSpace
attribute [local irreducible] intervalRetardedCriticalPath energyPath energyDistribution
  criticalGradient

section Abstract
variable {V : Type*} [NormedAddCommGroup V]

theorem l1_extension_tendsto_sub {f g : ℕ → V} {x y : V}
    (hf : Tendsto f atTop (𝓝 x)) (hg : Tendsto g atTop (𝓝 y)) :
    Tendsto (fun n => f n - g n) atTop (𝓝 (x-y)) := hf.sub hg

theorem l1_extension_tendsto_of_norm_sub {f : ℕ → V} {x : V}
    (hf : Tendsto (fun n => ‖f n - x‖) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 x) := tendsto_iff_norm_sub_tendsto_zero.mpr hf

end Abstract

/-- A convergent actual gradient sequence makes its actual retarded outputs Cauchy. -/
theorem intervalRetardedCriticalPath_cauchy_of_gradient_tendsto
    (hDensity : OrdinaryH1Density) {K C0 C a b : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C)
    (F : ℕ → CompatibleIntervalSource a b)
    (G : Fin 3 → LocalEndpointSource (Set.Icc a b))
    (hG : Tendsto (fun n => (F n).gradient) atTop (𝓝 G)) :
    CauchySeq (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (F n)) := by
  let Q := max (energyEndpointConstant K C0) C
  have hQ : 0 ≤ Q := (energyEndpointConstant_nonneg h0).trans (le_max_left _ _)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hG.cauchySeq (ε / (Q + 1))
    (div_pos hε (by linarith))
  refine ⟨N, fun m hm n hn => ?_⟩
  have hd := hN m hm n hn
  have hb := intervalRetardedCriticalPath_sub_norm hDensity hSob h0 h (F m) (F n)
  rw [dist_eq_norm] at hd
  rw [dist_eq_norm (intervalRetardedCriticalPath hDensity hSob h0 h (F m))
    (intervalRetardedCriticalPath hDensity hSob h0 h (F n))]
  change _ ≤ Q * _ at hb
  have hd' : (Q + 1) * ‖(F m).gradient - (F n).gradient‖ < ε :=
    by nlinarith [(lt_div_iff₀ (by linarith : 0 < Q + 1)).mp hd]
  nlinarith [norm_nonneg ((F m).gradient - (F n).gradient)]

namespace CompatibleL1IntervalSource
variable {a b : ℝ} (E : CompatibleL1IntervalSource a b)

/-- Cauchy is proved from the common-indicator approximation, never assumed. -/
theorem retarded_approximation_cauchy (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) :
    CauchySeq (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n)) :=
  intervalRetardedCriticalPath_cauchy_of_gradient_tendsto hDensity hSob h0 h
    E.approximation E.gradient E.approximation_gradient_tendsto

/-- A genuine member of the complete E+W graph, chosen from actual truncated outputs. -/
def retardedCriticalPath (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) : CriticalPath (intervalMeasure a b) :=
  limUnder atTop (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n))

theorem retarded_approximation_tendsto (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) :
    Tendsto (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n))
      atTop (𝓝 (E.retardedCriticalPath hDensity hSob h0 h)) :=
  (E.retarded_approximation_cauchy hDensity hSob h0 h).tendsto_limUnder

/-- The complete graph bound depends only on the original L2 gradient. -/
theorem retardedCriticalPath_norm_le (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) :
    ‖E.retardedCriticalPath hDensity hSob h0 h‖ ≤
      max (energyEndpointConstant K C0) C * ‖E.gradient‖ := by
  apply le_of_tendsto' (E.retarded_approximation_tendsto hDensity hSob h0 h).norm
  intro n
  exact (intervalRetardedCriticalPath_norm hDensity hSob h0 h (E.approximation n)).trans
    (mul_le_mul_of_nonneg_left (E.approximation_gradient_norm_le n)
      ((energyEndpointConstant_nonneg h0).trans (le_max_left _ _)))

/-- Every compatible L2 source is compared to the constructed output by its actual gradient error. -/
theorem intervalRetarded_sub_retardedCriticalPath_norm_le
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : CompatibleIntervalSource a b) :
    ‖intervalRetardedCriticalPath hDensity hSob h0 h F -
      E.retardedCriticalPath hDensity hSob h0 h‖ ≤
      max (energyEndpointConstant K C0) C * ‖F.gradient - E.gradient‖ := by
  apply le_of_tendsto_of_tendsto
    (l1_extension_tendsto_sub (V := CriticalPath (intervalMeasure a b))
      tendsto_const_nhds (E.retarded_approximation_tendsto hDensity hSob h0 h)).norm
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub E.approximation_gradient_tendsto).norm)
  exact Filter.Eventually.of_forall (fun n =>
    intervalRetardedCriticalPath_sub_norm hDensity hSob h0 h F (E.approximation n))

/-- The same output is obtained from any compatible approximation with convergent actual gradients. -/
theorem retarded_tendsto_of_gradient_tendsto
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : ℕ → CompatibleIntervalSource a b)
    (hF : Tendsto (fun n => (F n).gradient) atTop (𝓝 E.gradient)) :
    Tendsto (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (F n))
      atTop (𝓝 (E.retardedCriticalPath hDensity hSob h0 h)) := by
  apply l1_extension_tendsto_of_norm_sub (V := CriticalPath (intervalMeasure a b))
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => E.intervalRetarded_sub_retardedCriticalPath_norm_le hDensity hSob h0 h (F n))
  simpa only [mul_zero] using
    tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hF)

/-- Any limit of a valid compatible approximation is the canonical constructed output. -/
theorem retardedCriticalPath_eq_of_approximation
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (F : ℕ → CompatibleIntervalSource a b)
    (hF : Tendsto (fun n => (F n).gradient) atTop (𝓝 E.gradient))
    (u : CriticalPath (intervalMeasure a b))
    (hu : Tendsto (fun n => intervalRetardedCriticalPath hDensity hSob h0 h (F n)) atTop (𝓝 u)) :
    E.retardedCriticalPath hDensity hSob h0 h = u :=
  tendsto_nhds_unique (E.retarded_tendsto_of_gradient_tendsto hDensity hSob h0 h F hF) hu

/-- Native energy evaluation preserves the constructed convergence. -/
theorem retarded_approximation_energy_tendsto
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (t : Set.Icc a b) :
    Tendsto (fun n => energyPath _
      (intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n)) t)
      atTop (𝓝 (energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) t)) :=
  ((ContinuousMap.evalCLM ℂ t).comp (energyPath (intervalMeasure a b))).continuous.tendsto _
    |>.comp (E.retarded_approximation_tendsto hDensity hSob h0 h)

/-- Actual Schwartz testing of the output converges, ready for the literal scalar identification. -/
theorem retarded_approximation_scalar_tendsto
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (t : Set.Icc a b) (φ : FreeFlow.Test) :
    Tendsto (fun n => energyDistribution (energyPath _
      (intervalRetardedCriticalPath hDensity hSob h0 h (E.approximation n)) t) φ)
      atTop (𝓝 (energyDistribution (energyPath _
        (E.retardedCriticalPath hDensity hSob h0 h) t) φ)) :=
  ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ φ).comp energyDistribution).continuous.tendsto _
    |>.comp (E.retarded_approximation_energy_tendsto hDensity hSob h0 h t)

/-- The actual constructed path starts from zero at the left endpoint. -/
theorem retardedCriticalPath_initial (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (hab : a ≤ b) :
    energyPath _ (E.retardedCriticalPath hDensity hSob h0 h) ⟨a, le_rfl, hab⟩ = 0 := by
  apply tendsto_nhds_unique
    (E.retarded_approximation_energy_tendsto hDensity hSob h0 h ⟨a, le_rfl, hab⟩)
  have hz : (fun n => energyPath _ (intervalRetardedCriticalPath hDensity hSob h0 h
      (E.approximation n)) ⟨a, le_rfl, hab⟩) = fun _ : ℕ => (0 : EnergyState) := by
    funext n
    exact intervalRetardedCriticalPath_initial hDensity hSob h0 h hab (E.approximation n)
  rw [hz]
  exact tendsto_const_nhds

/-- Stability of the extension between two genuine L1-time sources. -/
theorem retardedCriticalPath_sub_norm_le (F : CompatibleL1IntervalSource a b)
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) :
    ‖E.retardedCriticalPath hDensity hSob h0 h - F.retardedCriticalPath hDensity hSob h0 h‖ ≤
      max (energyEndpointConstant K C0) C * ‖E.gradient - F.gradient‖ := by
  apply le_of_tendsto_of_tendsto
    (l1_extension_tendsto_sub (V := CriticalPath (intervalMeasure a b))
      (E.retarded_approximation_tendsto hDensity hSob h0 h)
      (F.retarded_approximation_tendsto hDensity hSob h0 h)).norm
    (tendsto_const_nhds.mul (E.approximation_gradient_tendsto.sub F.approximation_gradient_tendsto).norm)
  exact Filter.Eventually.of_forall (fun n => intervalRetardedCriticalPath_sub_norm hDensity hSob h0 h
    (E.approximation n) (F.approximation n))

theorem retardedCriticalPath_eq_of_gradient_eq (F : CompatibleL1IntervalSource a b)
    (hDensity : OrdinaryH1Density) {K C0 C : ℝ}
    (hSob : OrdinarySobolev K) (h0 : OrdinaryEndpointBound C0)
    (h : OrdinaryRetardedStrichartz h0 C) (hEF : E.gradient = F.gradient) :
    E.retardedCriticalPath hDensity hSob h0 h = F.retardedCriticalPath hDensity hSob h0 h := by
  apply sub_eq_zero.mp
  apply (norm_eq_zero (E := CriticalPath (intervalMeasure a b))).mp
  have hb := E.retardedCriticalPath_sub_norm_le F hDensity hSob h0 h
  have hz : ‖E.retardedCriticalPath hDensity hSob h0 h -
      F.retardedCriticalPath hDensity hSob h0 h‖ ≤ 0 := by
    simpa only [hEF, sub_self, norm_zero, mul_zero] using hb
  exact le_antisymm hz (norm_nonneg _)

end CompatibleL1IntervalSource
end HartreeF.ActualDuhamelPath
